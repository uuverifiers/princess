all:
	scalac -d bin/ -cp ".:org.sat4j.core.jar" src/ccu/CCUSolver.scala
	cd bin && jar cf ccu.jar ccu/ && cp ccu.jar ../../extlibs/ccu.jar
