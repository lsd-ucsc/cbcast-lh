all: build run
	docker ps

build:
	docker build . --tag nixops-target

run: kill
	docker network create --subnet=10.10.0.0/16 kv-net
	docker run -d --rm --name kv0 --ip=10.10.0.10 -p 127.0.0.1:7720:22 nixops-target # -p 127.0.0.1:7780:7780
	docker run -d --rm --name kv1 --ip=10.10.0.11 -p 127.0.0.1:7721:22 nixops-target # -p 127.0.0.1:7781:7780
	docker run -d --rm --name kv2 --ip=10.10.0.12 -p 127.0.0.1:7722:22 nixops-target # -p 127.0.0.1:7782:7780

kill:
	-docker stop kv0 kv1 kv2
	-docker network rm kv-net
