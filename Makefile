##  Makefile

IDRIS := idris
LIB   := commons
OPTS  :=

.PHONY: doc clobber check clean lib install

lib:
	${IDRIS} ${OPTS} --build ${LIB}.ipkg

install: lib
	${IDRIS} ${OPTS} --install ${LIB}.ipkg
	${IDRIS} ${OPTS} --installdoc ${LIB}.ipkg

clean:
	${IDRIS} --clean ${LIB}.ipkg
	find . -name "*~" -delete

check: clobber
	${IDRIS} --checkpkg ${LIB}.ipkg

clobber : clean
	find . -name "*.ibc" -delete

doc:
	${IDRIS} --mkdoc ${LIB}.ipkg
