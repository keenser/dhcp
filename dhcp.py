#!/usr/bin/env python3.5
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
#import codecs # v3.4

Field = namedtuple('Field', ('default', 'location', 'fmt', 'data'))
Option = namedtuple('Option', ('code', 'data'))
Hook = namedtuple('Hook', ('cmp', 'handler'))

class _bool(int):
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

class _8bits(int):
    def __new__(cls, value):
        if isinstance(value, str):
            value = int(value)
        elif isinstance(value, bytes):
            value = int.from_bytes(value, byteorder='big')
        return int.__new__(cls, value)
    def __bytes__(self):
        return self.to_bytes(1, byteorder='big')

class _16bits(_8bits):
    def __bytes__(self):
        return self.to_bytes(2, byteorder='big')

class _32bits(_8bits):
    def __bytes__(self):
        return self.to_bytes(4, byteorder='big')

class _string(bytes):
    def __new__(cls, value):
        if isinstance(value, str):
            value = value.encode('utf-8')
        return bytes.__new__(cls, value)
    def __str__(self):
        return self.decode('utf-8')

class _bytes(bytes):
    def __new__(cls, value):
        if isinstance(value, str):
            value = value.encode('utf-8')
        return bytes.__new__(cls, value)
    def __str__(self):
        #return '0x' + codecs.encode(self, 'hex').decode() # v3.4
        return '0x'+self.hex()

def _dict(dictionary):
    class _cdict():
        def __init__(self, value=None):
            self._data = int()
            if isinstance(value, (bytes, int)):
                self._data = _8bits(value)
            elif isinstance(value, str):
                self._data = _8bits(dictionary.get(value.upper(), None))
        def __str__(self):
            return list(dictionary.keys())[list(dictionary.values()).index(self._data)]
        def __bytes__(self):
            return bytes(self._data)
        def __eq__(self, other):
            return self._data == other or self._data == dictionary.get(other, None)
    return _cdict

def _dclist(dictionary={}):
    rdictionary = {val.code: key for key, val in dictionary.items()}
    class _clist():
        def __init__(self, value):
            self._data = {}
            if isinstance(value, dict):
                for field, opt in value.items():
                    tmpl = dictionary.get(field, Option(code=field, data=_string))
                    self._data[tmpl.code] = tmpl.data(opt)
            if isinstance(value, bytes):
                while value:
                    code = _8bits(value[:1])
                    tmpl = dictionary.get(rdictionary.get(code), Option(code=code, data=_string))
                    if tmpl.data:
                        length = _8bits(value[1:2])
                        if isinstance(tmpl.data, type):
                            self._data[code] = tmpl.data(value[2:2+length])
                        else:
                            self._data[code] = _bytes(value[2:2+length])
                        value = value[2+length:]
                    else:
                        value = value[1:]
        def __str__(self):
            return ', '.join(['%s: %s' % (rdictionary.get(field, field), opt) for field, opt in self._data.items()])
        def __bytes__(self):
            return b''.join([struct.pack('!2B', field, len(bytes(opt))) + bytes(opt) for field, opt in self._data.items()])
        def __iter__(self):
            for field, opt in self._data.items():
                yield [rdictionary.get(field, field), opt]
    return _clist

_list = _dclist()

class _prlist(tuple):
    def __new__(cls, value):
        if isinstance(value, bytes):
            value = list(value)
        elif isinstance(value, (tuple, list)):
            value = [int(OPTION.get(str(i).lower(), Option(code=i, data=None)).code) for i in value]
        elif isinstance(value, str):
            value = [int(OPTION.get(str(i).lower(), Option(code=i, data=None)).code) for i in value.split()]
        return tuple.__new__(cls, value)
    def __str__(self):
        return ' '.join([list(OPTION.keys())[[i.code for i in OPTION.values()].index(code)] for code in self])

class _chaddr(bytes):
    def __new__(cls, value):
        if isinstance(value, str):
            value = bytes.fromhex(value.replace(':', ''))
        return bytes.__new__(cls, value)
    def __str__(self):
        #return ':'.join(codecs.encode(self[i:i+1], 'hex').decode() for i in range(0, len(self))) # v3.4
        return ':'.join(map(lambda x: "%02x"%x, self))
        #return ':'.join(self[i:i+1].hex() for i in range(0, len(self)))

class _ipv4(ipaddress.IPv4Address):
    def __bytes__(self):
        return self.packed

class _ipv4plus(tuple):
    def __new__(cls, value):
        if isinstance(value, str):
            value = [ipaddress.IPv4Address(i) for i in value.split()]
        elif isinstance(value, (tuple, list)):
            value = [ipaddress.IPv4Address(i) for i in value]
        elif isinstance(value, bytes):
            value = [ipaddress.IPv4Address(value[i:i+4]) for i in range(0, len(value), 4)]
        return tuple.__new__(cls, value)
    def __str__(self):
        return ' '.join([str(i) for i in self])
    def __bytes__(self):
        return b''.join([i.packed for i in self])

class _ipv4vlsm(ipaddress.IPv4Network):
    def __init__(self, value):
        if isinstance(value, bytes):
            prefixlen = _8bits(value[:1])
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
        return ', '.join(["%s via %s" % (route[0], route[1]) for route in self])
    def __bytes__(self):
        return b''.join([bytes(route[0]) + bytes(route[1]) for route in self])

HEADER_FIELDS = OrderedDict()
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

OPTION = {}
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
OPTION['path_mtu_table'] = Option(code=25, data=_16bits) #fixit _16bitsplus
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
OPTION['nb_node_type'] = Option(code=46, data=_8bits)
OPTION['nb_scope'] = Option(code=47, data=_string)
OPTION['x_window_system_font_server'] = Option(code=48, data=_ipv4plus)
OPTION['x_window_system_display_manager'] = Option(code=49, data=_ipv4plus)
# DHCP extensions
OPTION['request_ip_address'] = Option(code=50, data=_ipv4)
OPTION['ip_address_lease_time'] = Option(code=51, data=_32bits)
OPTION['overload'] = Option(code=52, data=_8bits)
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
OPTION['netware_ip_sub_options'] = Option(code=63, data='RFC2242')
OPTION['nis+_domain'] = Option(code=64, data=_string)
OPTION['nis+_servers'] = Option(code=65, data=_ipv4plus)
OPTION['tftp_server_name'] = Option(code=66, data=_string)
OPTION['bootfile_name'] = Option(code=67, data=_string)
OPTION['mobile_ip_home_agent'] = Option(code=68, data=_ipv4)
OPTION['smtp_servers'] = Option(code=69, data=_ipv4plus)
OPTION['pop_servers'] = Option(code=70, data=_ipv4plus)
OPTION['nntp_servers'] = Option(code=71, data=_ipv4plus)
OPTION['default_www_server'] = Option(code=72, data=_ipv4plus)
OPTION['default_finger_server'] = Option(code=73, data=_ipv4plus)
OPTION['default_irc_server'] = Option(code=74, data=_ipv4plus)
OPTION['streettalk_server'] = Option(code=75, data=_ipv4plus)
OPTION['streettalk_directory_assistance_server'] = Option(code=76, data=_ipv4plus)
OPTION['user_class'] = Option(code=77, data='RFC3004')
OPTION['directory_agent'] = Option(code=78, data='RFC2610')
OPTION['service_scope'] = Option(code=79, data='RFC2610')
OPTION['rapid_commit'] = Option(code=80, data='null')
OPTION['client_fqdn'] = Option(code=81, data=_string)
OPTION['relay_agent'] = Option(code=82, data=_dclist({
        'CIRCUIT-ID': Option(code=1, data=_string),
        'REMOTE-ID': Option(code=2, data=_string)
    }))
OPTION['internet_storage_name_service'] = Option(code=83, data='RFC4174')
OPTION['84'] = Option(code=84, data=_bytes)
OPTION['nds_server'] = Option(code=85, data=_ipv4plus)
OPTION['nds_tree_name'] = Option(code=86, data='RFC2241')
OPTION['nds_context'] = Option(code=87, data='RFC2241')
OPTION['88'] = Option(code=88, data=_bytes)
OPTION['89'] = Option(code=89, data=_bytes)
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
OPTION['vendor_specific'] = Option(code=125, data=_bytes)
OPTION['end'] = Option(code=255, data=None)

_optlist = _dclist(OPTION)

class DHCP(object):
    def __init__(self):
        self.__hook = []
        self.dhcp_socket = self.CreateSocket(True, False)

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
    def CreateSocket(self, so_broadcast, so_reuseaddr) :
        dhcp_socket = None
        try :
            dhcp_socket = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        except (socket.error) as msg:
            sys.stderr.write('pydhcplib.DhcpNetwork socket creation error : '+str(msg))

        try :
            if so_broadcast :
                dhcp_socket.setsockopt(socket.SOL_SOCKET,socket.SO_BROADCAST,1)
        except (socket.error) as msg:
            sys.stderr.write('pydhcplib.DhcpNetwork socket error in setsockopt SO_BROADCAST : '+str(msg))

        try : 
            if so_reuseaddr :
                dhcp_socket.setsockopt(socket.SOL_SOCKET,socket.SO_REUSEADDR,1)
        except (socket.error) as msg:
            sys.stderr.write('pydhcplib.DhcpNetwork socket error in setsockopt SO_REUSEADDR : '+str(msg))

        return dhcp_socket

    def BindToAddress(self, listen_address="0.0.0.0", listen_port=67):
        try :
            self.dhcp_socket.bind((listen_address, listen_port))
        except (socket.error) as msg:
            sys.stderr.write( 'pydhcplib.DhcpNetwork.BindToAddress error : '+str(msg))

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

class Client(DHCP):
    def __init__(self, options):
        super().__init__()
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
            'request_ip_address': packet['yiaddr'],
            'server_identifier': packet['server_identifier']
        })

    def HandleDhcpAck(self, packet):
        self.__lock.set()

def main():
    client = Client({
            'chaddr': '00:1e:52:82:15:b7',
#            'listen':"192.168.1.13",
#            'server':'192.168.1.1',
#            'client_identifier':'test123',
            'parameter_request_list': [50, 51, 'classless_static_route'],
            'relay_agent': {'CIRCUIT-ID':'vci', 'REMOTE-ID':'vpi'},
            })
    client.SendPacket({'dhcp_message_type': 'DHCP_DISCOVER'})
    client.Wait()

if __name__ == '__main__':
    main()
