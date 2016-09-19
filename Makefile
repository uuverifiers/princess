

BASEDIR:=$(shell pwd)
EXTLIBSDIR:=$(BASEDIR)/extlibs

CLASSPATH:=$(CLASSPATH):$(BASEDIR)/parser/parser.jar:$(BASEDIR)/smt-parser/smt-parser.jar:$(EXTLIBSDIR)/java-cup-11a.jar:$(EXTLIBSDIR)/breu.jar
# :$(EXTLIBSDIR)/org.sat4j.core.jar

SCALAC:=scalac
SCALAC_OPTIONS:=-optimise -Yinline-warnings \
                -deprecation -unchecked \
                -feature -language:implicitConversions,postfixOps,reflectiveCalls \
                -d $(BASEDIR)/bin -classpath $(CLASSPATH)

SCALADOC:=scaladoc
SCALADOC_OPTIONS:=-doc-title Princess -d $(BASEDIR)/doc -classpath $(CLASSPATH)

JLEX_PATH:=/usr/share/java/JLex.jar

JAVAC:=javac
JAVAC_FLAGS:=-target 1.5

JAVA:=java
JAVA_FLAGS:=

# enough memory for the compiler on 64-bit architectures
JAVA_OPTS=-Xmx1G

# SCALABASEDIR:=/usr/local/scala
SCALABASEDIR:=/home/ptr/scala-2.11.7
SCALALIBDIR:=$(SCALABASEDIR)/lib

JARSIGNERCMD:=jarsigner -keystore ../myKeys -storepass ../myPass -keypass ../myPass
JARSIGNERALIAS:=mykey2015

# PROGUARDJAR:=/home/philipp/tmp/proguard/lib/proguard.jar
PROGUARDJAR:=/usr/share/java/proguard.jar


export SCALAC SCALAC_OPTIONS SCALADOC SCALADOC_OPTIONS JAVAC JAVAC_FLAGS JAVA JAVA_FLAGS CLASSPATH JLEX_PATH JAVA_OPTS


all: scala-src

doc: scala-src-doc

# This generates an empty scala-parser-combinators.jar file,
# since Scala 2.10 does not include this as a separate library,
# and Proguard needs it. With Scala 2.11, the empty jar file is
# overwritten in the next line
copy-jars-to-dist:
	$(shell cp bin/princess.jar dist/)
	$(shell cp parser/parser.jar dist/)
	$(shell cp smt-parser/smt-parser.jar dist/)
	$(shell cp $(EXTLIBSDIR)/java-cup-11a.jar dist/)
	$(shell cp $(EXTLIBSDIR)/breu.jar dist/)
#	$(shell cp $(EXTLIBSDIR)/org.sat4j.core.jar dist/)
#	$(shell cp $(EXTLIBSDIR)/scalaz.jar dist/)
#	$(shell cp $(EXTLIBSDIR)/argonaut.jar dist/)
	$(shell cp $(SCALALIBDIR)/scala-library.jar dist/)
	$(shell [ -f $(SCALALIBDIR)/scala-xml*.jar ] && cp $(SCALALIBDIR)/scala-xml*.jar dist/scala-xml.jar)
	$(shell [ -f $(SCALALIBDIR)/scala-actors-2*.jar ] && cp $(SCALALIBDIR)/scala-actors-2*.jar dist/scala-actors.jar)
	$(shell [ -f $(SCALALIBDIR)/scala-actors.jar ] && cp $(SCALALIBDIR)/scala-actors.jar dist/scala-actors.jar)
	$(shell [ -f $(SCALALIBDIR)/scala-parser-combinators*.jar ] && cp $(SCALALIBDIR)/scala-parser-combinators*.jar dist/scala-parser-combinators.jar)
	$(shell [ -f dist/scala-parser-combinators.jar ] || jar cf dist/scala-parser-combinators.jar dist/normal-manifest.txt)

jar: scala-src
	cd bin && jar cmf ../dist/normal-manifest.txt princess.jar ap

jar-assertionless: scala-src-assertionless
	cd bin && jar cf princess.jar ap

dist: jar copy-jars-to-dist
	java -jar $(PROGUARDJAR) @princess-proguard.pro

dist-assertionless: jar-assertionless copy-jars-to-dist
	java -jar $(PROGUARDJAR) @princess-proguard.pro

signed-dist: jar copy-jars-to-dist
	java -jar $(PROGUARDJAR) -dontusemixedcaseclassnames @princess-proguard.pro
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
