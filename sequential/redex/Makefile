all: test

TESTS=$(shell find . -name '*-test*.rkt' -exec echo {}.test \;)

test: ${TESTS}
	cat ${TESTS}

%.test: %
	raco make $^
	(time racket -t $^) &> $@

remake:
	rm -f ${TESTS}