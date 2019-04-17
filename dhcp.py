#!/usr/bin/env python3
#
# vim: tabstop=4 expandtab shiftwidth=4 softtabstop=4
#
import ipaddress
import struct
from collections import namedtuple, OrderedDict
import threading
import sys
import socket
import select
import os

Field = namedtuple('Field', ('default', 'location', 'fmt', 'data'))
Option = namedtuple('Option', ('code', 'data'))
Hook = namedtuple('Hook', ('cmp', 'handler'))
HEADER_FIELDS = OrderedDict()
OPTION = {}
OPTION6 = {}

class _bool(int):
    '''
    Input: _bool(True) _bool('True') _bool(b'0x01')
    Outupt: b'\x01'
    '''
    def __new__(cls, value=0):
        if isinstance(value, str):
            value = {'FALSE': 0, 'TRUE':1}[value.upper()]
        elif isinstance(value, bytes):
            value = int.from_bytes(value, byteorder='big')
        return int.__new__(cls, value)
    def __str__(self):
        return ['False', 'True'][self]
    def __bytes__(self):
        return self.to_bytes(1, byteorder='big')

class _zero():
    def __init__(self, value):
        pass
    def __str__(self):
        return ''
    def __bytes__(self):
        return b''

class _8bits(int):
    def __new__(cls, value):
        if isinstance(value, str):
            value = int(value)
        elif isinstance(value, bytes):
            value = int.from_bytes(value, byteorder='big')
        return int.__new__(cls, value)
    def __len__(self):
        return 1
    def __bytes__(self):
        return self.to_bytes(len(self), byteorder='big')

class _16bits(_8bits):
    def __len__(self):
        return 2

class _24bits(_8bits):
    def __len__(self):
        return 3

class _32bits(_8bits):
    def __len__(self):
        return 4

class _string(bytes):
    def __new__(cls, value):
        if isinstance(value, str):
            value = value.encode('utf-8')
        return bytes.__new__(cls, value)
    def __str__(self):
        return self.decode('utf-8')

class _fqdn(bytes):
    '''
    Input: _fqdn(['example.com.', 'test.org'])
    Outupt: b'\x07example\x03com\x00\x04test\x03org\x00'
    '''
    def __new__(cls, value):
        fqdn = b''
        if isinstance(value, str):
            value = value.split()
        if isinstance(value, (tuple, list)):
            for name in value:
                ds = name.split('.')
                if ds[-1] != '':
                    ds.append('')
                for d in ds:
                    dn = _string(d)
                    fqdn += bytes(_8bits(len(dn))) + dn
        elif isinstance(value, bytes):
            fqdn = value
        return bytes.__new__(cls, fqdn)
    def __str__(self):
        st = self
        names = []
        name = []
        while st:
            len = st[0]
            name.append(st[1:len+1])
            if len == 0:
                names.append(b'.'.join(name).decode('utf-8'))
                name = []
            st = st[len+1:]
        return ' '.join(names)

class _bytes(bytes):
    def __new__(cls, value):
        if isinstance(value, str):
            value = bytes(int(i) for i in value.split('.'))
        return bytes.__new__(cls, value)
    def __repr__(self):
        return self.__str__()
    def __str__(self):
        return '.'.join("%02d"%i for i in self)

def _dict(dictionary):
    '''
    Input: _dict({'A':1, 'B':2})('A')
    Outupt b'\x01'
    '''
    class _cdict():
        def __init__(self, value=None):
            self._data = int()
            if isinstance(value, (bytes, int)):
                self._data = _8bits(value)
            elif isinstance(value, str):
                self._data = _8bits(dictionary.get(value.upper(), None))
        def __repr__(self):
            return list(dictionary.keys())[list(dictionary.values()).index(self._data)]
        def __bytes__(self):
            return bytes(self._data)
        def __eq__(self, other):
            return self._data == other or self._data == dictionary.get(other, None)
    return _cdict

def _dclist(dictionary={}, hclass=_8bits):
    '''
    Input: _dclist({
                'CIRCUIT-ID': Option(code=1, data=_string),
                'REMOTE-ID': Option(code=2, data=_string)
            })({'CIRCUIT-ID':'AA', 2: 'BBB'})
    Output: b'\x01\x02AA\x02\x03BBB'
    '''
    hlen = len(hclass(0))
    class _clist():
        def __init__(self, value):
            self.rdictionary = {val.code: key for key, val in dictionary.items()}
            self._data = {}
            if isinstance(value, dict):
                for field, opt in value.items():
                    tmpl = dictionary.get(self.rdictionary.get(field, field), Option(code=field, data=_string))
                    self._data[tmpl.code] = tmpl.data(opt)
            elif isinstance(value, bytes):
                while value:
                    code = hclass(value[:hlen])
                    tmpl = dictionary.get(self.rdictionary.get(code), Option(code=code, data=_string))
                    if tmpl.data:
                        length = hclass(value[hlen:hlen+hlen])
                        if isinstance(tmpl.data, type):
                            self._data[code] = tmpl.data(value[2*hlen:2*hlen+length])
                        else:
                            self._data[code] = _bytes(value[2*hlen:2*hlen+length])
                        value = value[2*hlen+length:]
                    else:
                        value = value[hlen:]
        def __str__(self):
            return ', '.join('%s: %s' % (self.rdictionary.get(field, field), opt) for field, opt in self._data.items())
        def __bytes__(self):
            return b''.join(bytes(hclass(field)) + bytes(hclass(len(bytes(opt)))) + bytes(opt) for field, opt in self._data.items())
        def __iter__(self):
            for field, opt in self._data.items():
                yield [self.rdictionary.get(field, field), opt]
    return _clist

def _tmplprlist(dictionary={}, hclass=_8bits):
    '''
    Used for parameter_request_list(option 55) and path_mtu_table(option 25)
    Input: _tmplprlist({
                'VALUE5':  Option(code=5, data=_string)
            })([1, 'VALUE5', 6])
    Output: b'\x01\x05\x06'
    '''
    hlen = len(hclass(0))
    class _prlist(tuple):
        def __new__(cls, value):
            if isinstance(value, bytes):
                value = [hclass(value[i:i+hlen]) for i in range(0, len(value), hlen)]
            elif isinstance(value, (tuple, list)):
                value = [int(dictionary.get(str(i), Option(code=i, data=None)).code) for i in value]
            elif isinstance(value, str):
                value = [int(dictionary.get(str(i), Option(code=i, data=None)).code) for i in value.split()]
            return tuple.__new__(cls, value)
        def __init__(self, value):
            super().__init__()
            self.rdictionary = {val.code: key for key, val in dictionary.items()}
        def __bytes__(self):
            return b''.join(bytes(hclass(i)) for i in self)
        def __str__(self):
            return ' '.join(self.rdictionary.get(code, str(code)) for code in self)
    return _prlist

class _chaddr(bytes):
    def __new__(cls, value):
        if isinstance(value, str):
            value = bytes.fromhex(value.replace(':', ''))
        return bytes.__new__(cls, value)
    def __str__(self):
        return ':'.join("%02x"%i for i in self)

class _ipv4(ipaddress.IPv4Address):
    def __bytes__(self):
        return self.packed

class _ipv4plus(tuple):
    def __new__(cls, value):
        if isinstance(value, str):
            value = [_ipv4(i) for i in value.split()]
        elif isinstance(value, (tuple, list)):
            value = [_ipv4(i) for i in value]
        elif isinstance(value, bytes):
            value = [_ipv4(value[i:i+4]) for i in range(0, len(value), 4)]
        return tuple.__new__(cls, value)
    def __str__(self):
        return ' '.join(str(i) for i in self)
    def __bytes__(self):
        return b''.join(bytes(i) for i in self)

class _ipv4vlsm(ipaddress.IPv4Network):
    def __init__(self, value):
        if isinstance(value, bytes):
            prefixlen = value[0]
            netlen = - int( - prefixlen // 8 )
            net = value[1:1 + netlen] + bytes(4 - netlen)
            super().__init__(net)
            self.netmask, self._prefixlen = self._make_netmask(prefixlen)
        else:
            super().__init__(value)
    def __len__(self):
        return 1 - int( - self.prefixlen // 8 )
    def __bytes__(self):
        return bytes(_8bits(self.prefixlen)) + self.network_address.packed[:-int(-self.prefixlen//8)]

class _ipv4route(tuple):
    def __new__(cls, value):
        routelist = []
        if isinstance(value, str):
            value = value.split(', ')
        if isinstance(value, (tuple, list)):
            for data in value:
                if isinstance(data, str):
                    [net, gate] = data.split('via')
                    routelist.append([_ipv4vlsm(net.strip()), _ipv4(gate.strip())])
        elif isinstance(value, bytes):
            while value:
                net = _ipv4vlsm(value)
                netlen = len(net)
                gate = value[netlen: netlen + 4]
                routelist.append([net, _ipv4(gate)])
                value = value[netlen + 4:]
        return tuple.__new__(cls, routelist)
    def __str__(self):
        return ', '.join("%s via %s" % (route[0], route[1]) for route in self)
    def __bytes__(self):
        return b''.join(bytes(route[0]) + bytes(route[1]) for route in self)

class _ipv6(ipaddress.IPv6Address):
    def __bytes__(self):
        return self.packed

class _vendorlist():
    '''
    Input: _vendorlist([35265, {1:'mes'}])
    Output: b'\x00\x00\x89\xc1\x05\x01\x03mes'
    '''
    def __init__(self, value):
        if isinstance(value, (tuple, list)):
            self.option_code = _32bits(value[0])
            self.options = _list(value[1])
            self.option_len = _8bits(len(bytes(self.options)))
        elif isinstance(value, bytes):
            self.option_code = _32bits(value[:4])
            self.option_len = _8bits(value[4:5])
            self.options = _list(value[5:5+self.option_len])
    def __str__(self):
        return '%s: %s' % (self.option_code, self.options)
    def __bytes__(self):
        return bytes(self.option_code) + bytes(self.option_len) + bytes(self.options)

_list = _dclist()
_optlist = _dclist(OPTION)
_prlist = _tmplprlist(OPTION)
_16bitsplus = _tmplprlist({}, _16bits)

# Operation code, 1 request; 2 reply message
HEADER_FIELDS['op'] = Field(default=b'\x01', location=0, fmt='!1s', data=_dict({'ERROR_UNDEF':0 , 'BOOTREQUEST':1 , 'BOOTREPLY':2}))
# 1 is for hardware type ethernet
HEADER_FIELDS['htype'] = Field(default=b'\x01', location=1, fmt='!1s', data=_8bits)
# Hardware address length
HEADER_FIELDS['hlen'] = Field(default=b'\x06', location=2, fmt='!1s', data=_8bits)
# Amount of hops used via relay agents
HEADER_FIELDS['hops'] = Field(default=b'\x00', location=3, fmt='!1s', data=_8bits)
# Transaction Identifier, 32 bit client identifier generated by the client
HEADER_FIELDS['xid'] = Field(default=os.urandom(4), location=4, fmt='!4s', data=_32bits)
# Number of seconds elapsed since client began lease attempt
HEADER_FIELDS['secs'] = Field(default=b'\x00\x00', location=8, fmt='!2s', data=_16bits)
# Fuck knows
HEADER_FIELDS['flags'] = Field(default=b'\x00\x00', location=10, fmt='!2s', data=_16bits)
 # Client IP, only if client IP is valid in: BOUND, RENEWING or REBINDING states
HEADER_FIELDS['ciaddr'] = Field(default=b'\x00\x00\x00\x00', location=12, fmt='!4s', data=_ipv4)
# IP the server is assigning to the client
HEADER_FIELDS['yiaddr'] = Field(default=b'\x00\x00\x00\x00', location=16, fmt='!4s', data=_ipv4)
# The server address the next message should be sent to
HEADER_FIELDS['siaddr'] = Field(default=b'\x00\x00\x00\x00', location=20, fmt='!4s', data=_ipv4)
# Gateway IP address, facilitates for different subnet comm
HEADER_FIELDS['giaddr'] = Field(default=b'\x00\x00\x00\x00', location=24, fmt='!4s', data=_ipv4)
# Client hardware address, layer two, identification
HEADER_FIELDS['chaddr'] = Field(default=b'', location=28, fmt='!16s', data=_chaddr)
# Server name which is sending OFFER OR ACK. May be overloaded
HEADER_FIELDS['sname'] = Field(default=b'', location=44, fmt='!64s', data=_string)
# Optional boot file which client is requesting from server
HEADER_FIELDS['file'] = Field(default=b'', location=108, fmt='!128s', data=_string)
# RFC: 1048p2
HEADER_FIELDS['magic_cookie'] = Field(default=b'\x63\x82\x53\x63', location=236, fmt='!4s', data=_bytes)

OPTION['pad'] = Option(code=0, data=None)
# Vendor Extension
OPTION['subnet_mask'] = Option(code=1, data=_ipv4)
OPTION['time_offset'] = Option(code=2, data=_ipv4)
OPTION['router'] = Option(code=3, data=_ipv4plus)
OPTION['time_server'] = Option(code=4, data=_ipv4plus)
OPTION['name_server'] = Option(code=5, data=_ipv4plus)
OPTION['domain_name_server'] = Option(code=6, data=_ipv4plus)
OPTION['log_server'] = Option(code=7, data=_ipv4plus)
OPTION['cookie_server'] = Option(code=8, data=_ipv4plus)
OPTION['lpr_server'] = Option(code=9, data=_ipv4plus)
OPTION['impress_server'] = Option(code=10, data=_ipv4plus)
OPTION['resource_location_server'] = Option(code=11, data=_ipv4plus)
OPTION['host_name'] = Option(code=12, data=_string)
OPTION['boot_file'] = Option(code=13, data=_16bits)
OPTION['merit_dump_file'] = Option(code=14, data=_string)
OPTION['domain_name'] = Option(code=15, data=_string)
OPTION['swap_server'] = Option(code=16, data=_ipv4)
OPTION['root_path'] = Option(code=17, data=_string)
OPTION['extensions_path'] = Option(code=18, data=_string)
# IP layer parameters per host
OPTION['ip_forwarding'] = Option(code=19, data=_bool)
OPTION['nonlocal_source_rooting'] = Option(code=20, data=_bool)
OPTION['policy_filter'] = Option(code=21, data=_ipv4plus)
OPTION['maximum_datagram_reassembly_size'] = Option(code=22, data=_16bits)
OPTION['default_ip_time-to-live'] = Option(code=23, data=_8bits)
OPTION['path_mtu_aging_timeout'] = Option(code=24, data=_32bits)
OPTION['path_mtu_table'] = Option(code=25, data=_16bitsplus)
# IP layer parameters per interface
OPTION['interface_mtu'] = Option(code=26, data=_16bits)
OPTION['all_subnets_are_local'] = Option(code=27, data=_bool)
OPTION['broadcast_address'] = Option(code=28, data=_ipv4)
OPTION['perform_mask_discovery'] = Option(code=29, data=_bool)
OPTION['mask_supplier'] = Option(code=30, data=_bool)
OPTION['perform_router_discovery'] = Option(code=31, data=_bool)
OPTION['routeur_solicitation_address'] = Option(code=32, data=_ipv4)
OPTION['static_route'] = Option(code=33, data=_ipv4plus)
# link layer parameters per interface
OPTION['trailer_encapsulation'] = Option(code=34, data=_bool)
OPTION['arp_cache_timeout'] = Option(code=35, data=_32bits)
OPTION['ethernet_encapsulation'] = Option(code=36, data=_bool)
# TCP parameters
OPTION['tcp_default_ttl'] = Option(code=37, data=_8bits)
OPTION['tcp_keepalive_interval'] = Option(code=38, data=_32bits)
OPTION['tcp_keepalive_garbage'] = Option(code=39, data=_bool)
# Applications and service parameters
OPTION['nis_domain'] = Option(code=40, data=_string)
OPTION['nis_servers'] = Option(code=41, data=_ipv4plus)
OPTION['ntp_servers'] = Option(code=42, data=_ipv4plus)
OPTION['vendor_specific'] = Option(code=43, data=_string)
OPTION['nbns'] = Option(code=44, data=_ipv4plus)
OPTION['nbdd'] = Option(code=45, data=_ipv4plus)
OPTION['nb_node_type'] = Option(code=46, data=_dict({
        'B-node': 1, 'P-node': 2, 'M-node': 4, 'H-node': 8
    }))
OPTION['nb_scope'] = Option(code=47, data=_string)
OPTION['x_window_system_font_server'] = Option(code=48, data=_ipv4plus)
OPTION['x_window_system_display_manager'] = Option(code=49, data=_ipv4plus)
# DHCP extensions
OPTION['request_ip_address'] = Option(code=50, data=_ipv4)
OPTION['ip_address_lease_time'] = Option(code=51, data=_32bits)
OPTION['overload'] = Option(code=52, data=_dict({'file': 1, 'sname': 2, 'both': 3}))
OPTION['dhcp_message_type'] = Option(code=53, data=_dict({
        'DHCP_DISCOVER':1 , 'DHCP_OFFER':2 , 'DHCP_REQUEST':3 ,
        'DHCP_DECLINE':4 , 'DHCP_ACK':5 , 'DHCP_NACK':6 ,
        'DHCP_RELEASE':7 , 'DHCP_INFORM':8
    }))
OPTION['server_identifier'] = Option(code=54, data=_ipv4)
OPTION['parameter_request_list'] = Option(code=55, data=_prlist)
OPTION['message'] = Option(code=56, data=_string)
OPTION['maximum_dhcp_message_size'] = Option(code=57, data=_16bits)
OPTION['renewal_time_value'] = Option(code=58, data=_32bits)
OPTION['rebinding_time_value'] = Option(code=59, data=_32bits)
OPTION['vendor_class_identifier'] = Option(code=60, data=_string)
OPTION['client_identifier'] = Option(code=61, data=_chaddr)
# Add from RFC 2132
OPTION['netware_ip_domain_name'] = Option(code=62, data=_string)
OPTION['netware_ip_sub_options'] = Option(code=63, data=_dclist({
        'NWIP_DOES_NOT_EXIST': Option(code=1, data=_zero),
        'NWIP_EXIST_IN_OPTIONS_AREA': Option(code=2, data=_zero),
        'NWIP_EXIST_IN_SNAME_FILE': Option(code=3, data=_zero),
        'NWIP_EXIST_BUT_TOO_BIG': Option(code=4, data=_zero),
        'NSQ_BROADCAST': Option(code=5, data=_bool),
        'PREFERRED_DSS': Option(code=6, data=_ipv4plus),
        'NEAREST_NWIP_SERVER': Option(code=7, data=_ipv4plus),
        'AUTORETRIES': Option(code=8, data=_8bits),
        'AUTORETRY_SECS': Option(code=9, data=_8bits),
        'NWIP_1_1': Option(code=10, data=_bool),
        'PRIMARY_DSS': Option(code=11, data=_ipv4),
    }))
OPTION['nis+_domain'] = Option(code=64, data=_string)
OPTION['nis+_servers'] = Option(code=65, data=_ipv4plus)
OPTION['tftp_server_name'] = Option(code=66, data=_string)
OPTION['bootfile_name'] = Option(code=67, data=_string)
OPTION['mobile_ip_home_agent'] = Option(code=68, data=_ipv4plus)
OPTION['smtp_servers'] = Option(code=69, data=_ipv4plus)
OPTION['pop_servers'] = Option(code=70, data=_ipv4plus)
OPTION['nntp_servers'] = Option(code=71, data=_ipv4plus)
OPTION['default_www_server'] = Option(code=72, data=_ipv4plus)
OPTION['default_finger_server'] = Option(code=73, data=_ipv4plus)
OPTION['default_irc_server'] = Option(code=74, data=_ipv4plus)
OPTION['streettalk_server'] = Option(code=75, data=_ipv4plus)
OPTION['streettalk_directory_assistance_server'] = Option(code=76, data=_ipv4plus)
OPTION['user_class'] = Option(code=77, data=_list)
OPTION['directory_agent'] = Option(code=78, data='RFC2610')
OPTION['service_scope'] = Option(code=79, data='RFC2610')
OPTION['rapid_commit'] = Option(code=80, data=_zero)
OPTION['client_fqdn'] = Option(code=81, data=_string) # RFC4702
OPTION['relay_agent'] = Option(code=82, data=_dclist({
        'CIRCUIT-ID': Option(code=1, data=_string),
        'REMOTE-ID': Option(code=2, data=_string)
    }))
OPTION['internet_storage_name_service'] = Option(code=83, data='RFC4174')
OPTION['nds_server'] = Option(code=85, data=_ipv4plus)
OPTION['nds_tree_name'] = Option(code=86, data=_string)
OPTION['nds_context'] = Option(code=87, data=_string)
OPTION['BCMCS Controller Domain Name list'] = Option(code=88, data=_fqdn)
OPTION['BCMCS Controller IPv4 address option'] = Option(code=89, data=_ipv4plus)
OPTION['authentication'] = Option(code=90, data='RFC3118')
OPTION['client_last_transaction_time'] = Option(code=91, data='RFC4388')
OPTION['associated_ip'] = Option(code=92, data=_ipv4plus)
OPTION['client_system'] = Option(code=93, data=_bytes)
OPTION['client_ndi'] = Option(code=94, data=_bytes)
OPTION['ldap'] = Option(code=95, data=_bytes)
OPTION['uuid_guid'] = Option(code=97, data=_bytes)
OPTION['open_group_user_auth'] = Option(code=98, data=_string)
OPTION['netinfo_address'] = Option(code=112, data=_bytes)
OPTION['netinfo_tag'] = Option(code=113, data=_bytes)
OPTION['url'] = Option(code=114, data=_bytes)
OPTION['auto_config'] = Option(code=116, data=_8bits)
OPTION['name_service_search'] = Option(code=117, data='RFC2937')
OPTION['subnet_selection'] = Option(code=118, data=_ipv4)
OPTION['domain_search'] = Option(code=119, data='RFC3397')
OPTION['sip_servers'] = Option(code=120, data='RFC3361')
OPTION['classless_static_route'] = Option(code=121, data=_ipv4route)
OPTION['cablelabs_client_configuration'] = Option(code=122, data=_bytes)
OPTION['geoconf'] = Option(code=123, data=_bytes)
OPTION['vendor_class'] = Option(code=124, data=_bytes)
OPTION['vi-vendor_specific'] = Option(code=125, data=_vendorlist)
OPTION['end'] = Option(code=255, data=None)

class DHCP(object):
    def __init__(self, eth=None):
        self.__hook = []
        self.dhcp_socket = self.CreateSocket(True, False, eth)

    @staticmethod
    def serialize(option):
        """ Convert string to bytestring used in UDP packet
            We assume at this point all fields which will be sent are specified
            and of proper size and format.
        """

        data = bytearray(240)

        for field, opt in HEADER_FIELDS.items():
            struct.pack_into(opt.fmt, data, opt.location, bytes(opt.data(option.pop(field, opt.default))))
        data += bytes(_optlist(option))
        data += bytes(_8bits(OPTION['end'].code))

        return data

    @staticmethod
    def deserialize(data):
        option = OrderedDict()
        for field, opt in HEADER_FIELDS.items():
            option[field] = opt.data(struct.unpack_from(opt.fmt, data, opt.location)[0])
        option.update(_optlist(data[240:]))

        return option

    # Networking stuff
    def CreateSocket(self, so_broadcast, so_reuseaddr, so_eth) :
        sock = None
        try :
            sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        except (socket.error) as msg:
            sys.stderr.write('pydhcplib.DhcpNetwork socket creation error : '+str(msg))

        try :
            if so_broadcast :
                sock.setsockopt(socket.SOL_SOCKET,socket.SO_BROADCAST,1)
        except (socket.error) as msg:
            sys.stderr.write('pydhcplib.DhcpNetwork socket error in setsockopt SO_BROADCAST : '+str(msg))

        try :
            if so_reuseaddr :
                sock.setsockopt(socket.SOL_SOCKET,socket.SO_REUSEADDR,1)
        except (socket.error) as msg:
            sys.stderr.write('pydhcplib.DhcpNetwork socket error in setsockopt SO_REUSEADDR : '+str(msg))

        try:
            if so_eth :
                sock.setsockopt(socket.SOL_SOCKET, socket.SO_BINDTODEVICE, str(so_eth + '\0').encode('utf-8'))
        except (socket.error) as msg:
            sys.stderr.write('pydhcplib.DhcpNetwork socket error in setsockopt SO_BINDTODEVICE : '+str(msg))
        except AttributeError as msg:
            pass

        return sock

    def BindToAddress(self, listen_address="0.0.0.0", listen_port=67):
        try :
            self.dhcp_socket.bind((listen_address, listen_port))
        except (socket.error) as msg:
            sys.stderr.write('pydhcplib.DhcpNetwork.BindToAddress error : '+str(msg))

    def SendDhcpPacketTo(self, packet, _ip, _port):
        return self.dhcp_socket.sendto(packet,(_ip,_port))

    def AddHook(self, _cmp, _handler):
        #if isinstance(_cmp, function) and isinstance(_handler, function):
        self.__hook.append(Hook(cmp=_cmp, handler=_handler))

    def GetNextDhcpPacket(self,timeout=60):
        while True:
            data_input, data_output, data_except = select.select([self.dhcp_socket],[],[],timeout)
            if( data_input != [] ):
                (data, source_address) = self.dhcp_socket.recvfrom(2048)
                if data != "":
                    packet = self.deserialize(data)
                    for hook in self.__hook:
                        if hook.cmp(packet):
                            hook.handler(packet)

OPTION6['CLIENTID'] = Option(code=1, data=_bytes)
OPTION6['SERVERID'] = Option(code=2, data=_bytes)
OPTION6['IA_NA'] = Option(code=3, data=_bytes)
OPTION6['IA_TA'] = Option(code=4, data=_bytes)
OPTION6['IAADDR'] = Option(code=5, data=_bytes)
OPTION6['ORO'] = Option(code=6, data=_bytes)
OPTION6['PREFERENCE'] = Option(code=7, data=_bytes)
OPTION6['ELAPSED_TIME'] = Option(code=8, data=_bytes)
OPTION6['RELAY_MSG'] = Option(code=9, data=_bytes)
OPTION6['AUTH'] = Option(code=11, data=_bytes)
OPTION6['UNICAST'] = Option(code=12, data=_bytes)
OPTION6['STATUS_CODE'] = Option(code=13, data=_bytes)
OPTION6['RAPID_COMMIT'] = Option(code=14, data=_bytes)
OPTION6['USER_CLASS'] = Option(code=15, data=_bytes)
OPTION6['VENDOR_CLASS'] = Option(code=16, data=_bytes)
OPTION6['VENDOR_OPTS'] = Option(code=17, data=_bytes)
OPTION6['INTERFACE_ID'] = Option(code=18, data=_bytes)
OPTION6['RECONF_MSG'] = Option(code=19, data=_bytes)
OPTION6['RECONF_ACCEPT'] = Option(code=20, data=_bytes)

_optlistv6 = _dclist(OPTION6, _16bits)
_prlistv6 = _tmplprlist(OPTION6, _16bits)

class DHCPv6(DHCP):
    @staticmethod
    def serialize(option):
        data += bytes(_optlistv6(option))
        return data

    @staticmethod
    def deserialize(data):
        option = OrderedDict()

        option['msg-type'] = _dict({
            'SOLICIT':1, 'ADVERTISE':2, 'REQUEST':3, 'CONFIRM':4,
            'RENEW':5, 'REBIND':6, 'REPLY':7, 'RELEASE':8, 'DECLINE':9,
            'RECONFIGURE':10, 'INFORMATION-REQUEST':11, 'RELAY-FORW':12,
            'RELAY-REPL':13,
        })(data[0])
        if option['msg-type'] == 'RELAY-FORW' or option['msg-type'] == 'RELAY-REPL':
            option['hop-count'] = _8bits(data[1])
            option['link-address'] = _ipv6(data[2:18])
            option['peer-address'] = _ipv6(data[18:34])
            option.update(_optlistv6(data[34:]))
        else:
            option['transaction-id'] = _24bits(data[1:4])
            option.update(_optlistv6(data[4:]))

        return option

    # Networking stuff
    def CreateSocket(self, so_broadcast, so_reuseaddr) :
        sock = None
        sock = socket.socket(socket.AF_INET6, socket.SOCK_DGRAM)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        sock.setsockopt(socket.IPPROTO_IPV6, socket.IPV6_MULTICAST_HOPS, 1)
        sock.setsockopt(socket.IPPROTO_IPV6, socket.IPV6_MULTICAST_LOOP, 0)
        return sock

    def BindToAddress(self, listen_address="ff02::1:2", listen_port=547):
        super().BindToAddress(listen_address, listen_port)

    def SendDhcpPacketTo(self, packet, _ip, _port):
        return self.dhcp_socket.sendto(packet,(_ip,_port))

#a = DHCPv6()
#print(a.deserialize(b'\x01\x00\x00\x02\x00\x01\x00\x0e\x00\x01\x00\x01\x1em|/\x00\x0c\x01\x02\x03\x04\x00\x03\x00\x0c\x00\x00\x00\x01\x00\x00\x0e\x10\x00\x00\x15\x18\x00\x06\x00\x04\x00\x17\x00\x18\x00\x08\x00\x02\x00\x00'))
#print(a.deserialize(b'\x0c\x01 \x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01 \x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02\x00\x08\x00\x02\x00\x00'))
#a.BindToAddress()

class Client(DHCP):
    def __init__(self, options):
        self.device = options.pop('device', None)
        self.server = options.pop('server', '255.255.255.255')
        self.server_port = options.pop('server_port', 67)
        self.listen = options.pop('listen', '0.0.0.0')
        self.client_port = options.pop('client_port', None)
        self.options = options
        self.options.setdefault('giaddr', self.listen)

        if self.client_port is None:
            if self.listen == '0.0.0.0':
                self.client_port = 68
            else:
                self.client_port = 67

        self.__lock = threading.Event()

        super().__init__(self.device)
        self.AddHook(lambda packet: True, self.HandleDhcpAll)
        self.AddHook(lambda packet: packet.get('dhcp_message_type') == 'DHCP_OFFER', self.HandleDhcpOffer)
        self.AddHook(lambda packet: packet.get('dhcp_message_type') == 'DHCP_ACK', self.HandleDhcpAck)

        self.BindToAddress(self.listen, self.client_port)
        self.th = threading.Thread(target=self.GetNextDhcpPacket)
        self.th.daemon = True
        self.th.start()

    def Wait(self, wait=5):
        self.__lock.wait(wait)

    def SendPacket(self, options = {}):
        self.SendDhcpPacketTo(self.serialize({**self.options, **options}), self.server, self.server_port)

    def HandleDhcpAll(self, packet):
        for key, val in packet.items():
            print(key, val)

    def HandleDhcpOffer(self, packet):
        self.SendPacket({
            'dhcp_message_type': 'DHCP_REQUEST',
            'request_ip_address': packet.get('yiaddr'),
            'server_identifier': packet.get('server_identifier')
        })

    def HandleDhcpAck(self, packet):
        self.__lock.set()

def main():
    #use encapsulated vendor-specific extensions:
    OPTION['vendor_specific'] = Option(code=43, data=_list)
    client = Client({
            #'device': 'eth0',
            'chaddr': '00:1e:52:82:15:b7',
            #'listen':"192.168.10.21",
            #'server':'192.168.10.5',
            #'server_port':67,
            #'request_ip_address': '192.168.10.20',
            #'client_identifier':'test123',
            #'parameter_request_list': [50, 51, 'classless_static_route'],
            #'parameter_request_list': [125],
            #'relay_agent': {'CIRCUIT-ID':'eltex-1-1 eth 100/1:100', 'REMOTE-ID':'vpi'},
            #'vendor_specific': {1:'vs1', 2:'vs2'},
            #'path_mtu_table': "1000 2000",
            })
    client.SendPacket({'dhcp_message_type': 'DHCP_DISCOVER'})
    client.Wait()

if __name__ == '__main__':
    main()
