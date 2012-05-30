package ap.parameterInference

import java.io.File
import java.io.ObjectInputStream
import java.io.FileInputStream
import weka.classifiers.bayes.NaiveBayes
import weka.core.Instance
import weka.core.converters.ConverterUtils.DataSource
import weka.filters.unsupervised.attribute.Remove
import weka.filters.Filter
import ap.parameters.{GlobalSettings,Param}
//import scala.util.Sorting

class MyClassifier() {
  
  val clsPath=new java.io.File("models/")
  
  //Currently doesn't store models, but for multiple instances it could be faster to store them for a while
  def classify(Attributes : Array[Double]):Array[(java.lang.String,Double)]={
    
  val files=clsPath.listFiles().filter(x => x.getPath().endsWith(".model"))
  
  val res=Array.fill(files.size)("",0.0)
  var j=0
  var k=0
  var cls = new NaiveBayes();
  for (clsPath <- files) {
    
    try {
    val ois= new ObjectInputStream(new FileInputStream(clsPath.getAbsolutePath));
    cls = ois.readObject().asInstanceOf[NaiveBayes];
    ois.close();
    } catch { case e : Throwable => println("Error")}
    
    val instance=new Instance(Attributes.size+2);
    for ( i <- 0 until Attributes.size){
      instance.setValue(i,Attributes(i))
    }
    
    val instSet = (new DataSource("/home/aleks/models/emptyDataSet.arff")).getDataSet
    if (instSet.classIndex() == -1)
		instSet.setClassIndex(instSet.numAttributes() - 1);
   
    instance.setDataset(instSet)
    instSet.add(instance)
   
    val options = weka.core.Utils.splitOptions("-R 1-21,38,44,66-67,70,76-82");

    
	val remove = new Remove();                         // new instance of filter
	remove.setOptions(options);                           // set options
	remove.setInputFormat(instSet); 
	
	val newData = Filter.useFilter(instSet, remove);
	
	val inst = newData.firstInstance
	inst.setClassMissing()
	
    val pair=cls.distributionForInstance(inst)
    val name=clsPath.getName
    res(j)=(name.substring(0,name.indexOf('.')),pair(1)-pair(0))
    j+=1
  } 
 
  scala.util.Sorting.stableSort(res,(x,y)=>x._2>y._2)
    
    
    //Array[(String,Double)](("",0.0))
  }
  
  
  def strategyToOptions(strategy : String, base:GlobalSettings):GlobalSettings={
    
    
   /* if (strategy.length!=7 || strategy.toList.filter(x => (x=='0') || (x =='1') || (x=='2') )!="")
      null
    else{*/
       var s = base
       if (strategy.charAt(0)=='0')
       s = Param.TRIGGERS_IN_CONJECTURE.set(s, false)
       else { s = Param.TRIGGERS_IN_CONJECTURE.set(s, true) }
       
       if (strategy.charAt(1)=='0')
         s = Param.GENERATE_TOTALITY_AXIOMS.set(s, false)
       else {s = Param.GENERATE_TOTALITY_AXIOMS.set(s, true)}
       
       if (strategy.charAt(2)=='0')
       s = Param.TIGHT_FUNCTION_SCOPES.set(s, false)
       else {s = Param.TIGHT_FUNCTION_SCOPES.set(s, true)}
       
       if (strategy.charAt(3)=='0')
       s = Param.CLAUSIFIER.set(s, Param.ClausifierOptions.Simple)
       else {s = Param.CLAUSIFIER.set(s, Param.ClausifierOptions.None)}
       
       if (strategy.charAt(4)=='0')
       s = Param.REVERSE_FUNCTIONALITY_PROPAGATION.set(s, false)
       else { s = Param.REVERSE_FUNCTIONALITY_PROPAGATION.set(s, true)}

       if(strategy.charAt(5)=='0')
       s = Param.BOOLEAN_FUNCTIONS_AS_PREDICATES.set(s, false)
       else {s = Param.BOOLEAN_FUNCTIONS_AS_PREDICATES.set(s, true)}
       
       if(strategy.charAt(6)=='0')
       s = Param.TRIGGER_STRATEGY.set(s, Param.TriggerStrategyOptions.AllMaximal)
       else if(strategy.charAt(6)=='1')
       s = Param.TRIGGER_STRATEGY.set(s, Param.TriggerStrategyOptions.Maximal)
       else {s = Param.TRIGGER_STRATEGY.set(s, Param.TriggerStrategyOptions.AllMinimal)} 
       s
   // }
  }
    def strategyName(strategy : String):String={
    
    /*if (strategy.length!=7 || strategy.toList.filter(x => (x=='0') || (x =='1') || (x=='2') )!="")
      "Unknown"
    else{*/
       var s = ""
       if (strategy.charAt(0)=='0')
       s = s + " -triggersInConjencture"
       else { s = s + " +triggersInConjencture" }
       
       if (strategy.charAt(1)=='0')
       s = s + " -genTotalityAxioms"
       else { s = s + " +genTotalityAxioms" }
       
       if (strategy.charAt(2)=='0')
       s = s + " -tightFunctionScopes"
       else {s = s + " +tightFunctionScopes"}
       
       if (strategy.charAt(3)=='0')
       s = s + " -clausifier=simple"
       else { s = s + " -clausifier=none" }
       
       if (strategy.charAt(4)=='0')
       s = s + " -reverseFunctionalityPropagation"
       else { s = s + " +reverseFunctionalityPropagation" }

       if(strategy.charAt(5)=='0')
       s = s + " -boolFunsAsPreds"
       else { s = s + "+boolFunsAsPreds" }
       
       if(strategy.charAt(6)=='0')
       s = s + " -triggerStrategy=AllMaximal"
       else if(strategy.charAt(6)=='1')
       s = s + " -triggerStrategyMaximal"
       else { s = s + " -triggerStrategy=Minimal"} 
       s
    }
   // }
  
  
}