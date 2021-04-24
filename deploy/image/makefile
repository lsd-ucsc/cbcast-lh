
build:
	docker build . --tag nixops-target

run:
	docker run --publish-all --rm --name kv0 nixops-target

kill:
	docker kill kv0 kv1 kv2
