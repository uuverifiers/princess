

BASEDIR:=$(shell pwd)
EXTLIBSDIR:=$(BASEDIR)/extlibs

CLASSPATH:=$(CLASSPATH):$(BASEDIR)/parser/parser.jar:$(BASEDIR)/smt-parser/smt-parser.jar:$(EXTLIBSDIR)/java-cup-11a.jar

SCALAC:=scalac
SCALAC_OPTIONS:=-deprecation -unchecked -d $(BASEDIR)/bin -classpath $(CLASSPATH)

SCALADOC:=scaladoc
SCALADOC_OPTIONS:=-doc-title Princess -d $(BASEDIR)/doc -classpath $(CLASSPATH)

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

PROGUARDJAR:=/home/philipp/tmp/proguard4.6/lib/proguard.jar


export SCALAC SCALAC_OPTIONS SCALADOC SCALADOC_OPTIONS JAVAC JAVAC_FLAGS JAVA JAVA_FLAGS CLASSPATH JLEX_PATH JAVA_OPTS


all: scala-src

doc: scala-src-doc

jar: scala-src
	cd bin && jar cf princess.jar ap

dist: jar
	$(shell cp bin/princess.jar dist/)
	$(shell cp parser/parser.jar dist/)
	$(shell cp smt-parser/smt-parser.jar dist/)
	$(shell cp $(EXTLIBSDIR)/java-cup-11a.jar dist/)
	$(shell cp $(SCALALIBDIR)/scala-library.jar dist/)
	java -jar $(PROGUARDJAR) @princess-proguard.pro

jar-assertionless: scala-src-assertionless
	cd bin && jar cf princess.jar ap

dist-assertionless: jar-assertionless
	$(shell cp bin/princess.jar dist/)
	$(shell cp parser/parser.jar dist/)
	$(shell cp smt-parser/smt-parser.jar dist/)
	$(shell cp $(EXTLIBSDIR)/java-cup-11a.jar dist/)
	$(shell cp $(SCALALIBDIR)/scala-library.jar dist/)
	java -jar $(PROGUARDJAR) @princess-proguard.pro

signed-dist: dist
	$(JARSIGNERCMD) dist/princess-all.jar $(JARSIGNERALIAS)

clean:
	rm -rf bin
	rm -rf doc
	rm -rf dist/*.jar
	cd parser && $(MAKE) clean
	cd smt-parser && $(MAKE) clean

scala-src:
	$(shell [ -d bin ] || mkdir bin)
	cd src && $(MAKE)

scala-src-doc:
	$(shell [ -d doc ] || mkdir doc)
	cd src && $(MAKE) doc

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

smt-parser-jar:
	cd smt-parser && $(MAKE)

smtlib-pdf:
	cd smt-parser && $(MAKE) smtlib.pdf
