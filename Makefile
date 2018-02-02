all: install

install: build
	idris --install homology.ipkg

build: 
	idris --build homology.ipkg

test: build
	(cd tests; bash runtests.sh)

clean:
	idris --clean homology.ipkg
	rm -f tests/*.ibc
