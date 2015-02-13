all:
	scalac -d bin/ -cp ".:org.sat4j.core.jar" src/ccu/CCUSolver.scala src/ccu/LazySolver.scala src/ccu/Util.scala src/ccu/TableSolver.scala src/ccu/Timer.scala src/ccu/Timeout.scala
	cd bin && jar cf ccu.jar ccu/ && cp ccu.jar ../../extlibs/ccu.jar
