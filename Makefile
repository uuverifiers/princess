

BASEDIR:=$(shell pwd)
EXTLIBSDIR:=$(BASEDIR)/extlibs

SCALAC:=scalac
SCALAC_OPTIONS:=-deprecation -unchecked -d $(BASEDIR)/bin -classpath $(BASEDIR)/parser/parser.jar:$(EXTLIBSDIR)/java-cup-11a.jar

CLASSPATH:=$(CLASSPATH):$(BASEDIR)/parser/parser.jar:$(EXTLIBSDIR)/java-cup-11a.jar

JLEX_PATH:=/usr/share/java/JLex.jar

JAVAC:=javac
JAVAC_FLAGS:=-target 1.5

JAVA:=java
JAVA_FLAGS:=

# enough memory for the compiler on 64-bit architectures
JAVA_OPTS=-Xmx1G

SCALABASEDIR:=/usr/local/scala
SCALALIBDIR:=$(SCALABASEDIR)/lib

JARSIGNERCMD:=jarsigner -keystore ../myKeys -storepass ../myPass -keypass ../myPass
JARSIGNERALIAS:=phr


export SCALAC SCALAC_OPTIONS JAVAC JAVAC_FLAGS JAVA JAVA_FLAGS CLASSPATH JLEX_PATH JAVA_OPTS


all: scala-src

jar: scala-src
	cd bin && jar cf princess.jar ap

dist: jar
	$(shell cp bin/princess.jar dist/)
	$(shell cp parser/parser.jar dist/)
	$(shell cp $(EXTLIBSDIR)/java-cup-11a.jar dist/)
	$(shell cp $(SCALALIBDIR)/scala-library.jar dist/)
	$(JARSIGNERCMD) dist/princess.jar $(JARSIGNERALIAS)
	$(JARSIGNERCMD) dist/parser.jar $(JARSIGNERALIAS)
	$(JARSIGNERCMD) dist/java-cup-11a.jar $(JARSIGNERALIAS)
	$(JARSIGNERCMD) dist/scala-library.jar $(JARSIGNERALIAS)

clean:
	rm -rf bin
	cd parser && $(MAKE) clean

scala-src:
	$(shell [ -d bin ] || mkdir bin)
	cd src && $(MAKE)

gen-src-assertionless:
	rm -rf src_assertionless
	cd src && ./genSrcAssertionless
	cd src_assertionless && ln -s ../src/Makefile .

scala-src-assertionless: gen-src-assertionless
	$(shell [ -d bin ] || mkdir bin)
	cd src_assertionless && $(MAKE)

parser-jar:
	cd parser && $(MAKE)

ApInput-pdf:
	cd parser && $(MAKE) ApInput.pdf
