#!/usr/bin/env python3

# what's the amplification factor?

client_req = 1e4

target_process_minutes = 8

while True:

    servers = 8.
    clients_per_server = 3.
    print(f'{servers:10.8} servers')
    print(f'{clients_per_server * servers:10.8} clients')

    print(f'{client_req:10.8} requests sent by each client')
    message_req_fraction = 2.0/3.0 # PUT, DELETE, GET

    server_reqs = clients_per_server * client_req
    print(f'{server_reqs:10.8} requests received by each server')
    print(f'{message_req_fraction:10.8} fraction of requests which require a broadcast')

    server_message_reqs = server_reqs * message_req_fraction
    print(f'{server_message_reqs:10.8} broadcasts sent by each server')
    server_broadcasts = server_message_reqs

    # ignore unicasts; how many broadcasts does each server receive?

    received_broadcasts = server_broadcasts * (servers - 1)
    print(f'{received_broadcasts:10.8} messages received by each server')

    server_rate = 91244.625 / (19 * 60 + 30) # msg/sec
    print(f'{server_rate:10.8} messages processed per sec by server in 8 + 8*3 cluster (slow, maybe because it\'s network bound?')

    process_time_minutes = received_broadcasts * (1/server_rate) * (1.0/60.0)
    # msg * sec * min
    #  1    msg   sec
    print(f'{process_time_minutes:10.8} minutes estimated processing')

    if abs(process_time_minutes - target_process_minutes) < 1:
        break
    elif process_time_minutes < target_process_minutes:
        client_req = 1.01 * client_req # process more
    elif target_process_minutes < process_time_minutes:
        client_req = 0.9 * client_req # process less
