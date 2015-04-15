CCUDIR:=src/main/scala/ccu

pack:
	sbt assembly
	mv target/scala-2.10/BREU-assembly-0.1-SNAPSHOT.jar ../extlibs/ccu.jar

all:
	scalac -d "bin/" -cp "./lib/org.sat4j.core.jar:" $(CCUDIR)/*.scala
	cd bin && jar cf ccu.jar ccu/ && cp ccu.jar ../../extlibs/ccu.jar


