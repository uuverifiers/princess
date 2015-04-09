CCUDIR:=src/main/scala/ccu

all:
	scalac -d "bin/" -cp "./lib/org.sat4j.core.jar:" $(CCUDIR)/*.scala
	cd bin && jar cf ccu.jar ccu/ && cp ccu.jar ../../extlibs/ccu.jar
