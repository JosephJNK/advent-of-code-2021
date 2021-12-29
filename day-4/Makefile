.PHONY: build

default:
	make clean
	make build
	make run

run:
	node build/Main.js

build:
	dafny /compileTarget:js /out:build/Main.js src/*.dfy js/*.js
	cp -r js build

clean:
	rm -rf build
	mkdir build
