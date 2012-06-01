package ap.parameterInference

import java.io.File
import java.io.ObjectInputStream
import java.io.FileInputStream

import weka.classifiers.bayes.NaiveBayes
import weka.core.Instance
import weka.core.converters.ConverterUtils.DataSource
import weka.filters.unsupervised.attribute.Remove
import weka.filters.Filter

import scala.collection.mutable.ArrayBuffer

import ap.parameters.{GlobalSettings,Param}
//import scala.util.Sorting

object MyClassifier {

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
       s = s + " -triggersInConjecture"
       else { s = s + " +triggersInConjecture" }
       
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
       else { s = s + " +boolFunsAsPreds" }
       
       if(strategy.charAt(6)=='0')
       s = s + " -triggerStrategy=AllMaximal"
       else if(strategy.charAt(6)=='1')
       s = s + " -triggerStrategyMaximal"
       else { s = s + " -triggerStrategy=Minimal"} 
       s
    }
   // }

  //////////////////////////////////////////////////////////////////////////////
    
  object ResourceFiles {

    private val modelsListFile = "/models/models.list"
    private val emptyDataSetFile = "/models/emptyDataSet.arff"
    
    private def allModels = {
      val reader = toReader(resourceAsStream(modelsListFile))
      val res = new ArrayBuffer[String]
      
      var name = reader.readLine
      while (name != null) {
        res += name
        name = reader.readLine
      }
      
      res.toSeq
    }
    
    def modelInputStreams =
      for (file <- allModels.iterator) yield
        ((file split '/').last, resourceAsStream(file))
    
    def emptyDataSetStream =
      resourceAsStream(emptyDataSetFile)
    
    private def toReader(stream : java.io.InputStream) =
      new java.io.BufferedReader (new java.io.InputStreamReader(stream))

    private def resourceAsStream(filename : String) =
      ResourceFiles.getClass.getResourceAsStream(filename)
//      new java.io.FileInputStream(filename)
  }

  //////////////////////////////////////////////////////////////////////////////
  
  def classify(Attributes : Seq[Double]) : Seq[String] =
    (for ((name, modelStream) <- ResourceFiles.modelInputStreams) yield {
      val cls = try {
        val ois = new ObjectInputStream(modelStream)
        val cls = ois.readObject().asInstanceOf[NaiveBayes]
        ois.close()
        cls
      } catch {
        case e : Throwable =>
          throw new Exception("could not read Bayesian model: " + e.getMessage)
      }
      
      val instance = new Instance(Attributes.size + 2)
      for ((a, i) <- Attributes.iterator.zipWithIndex)
        instance.setValue(i, a)
      
      val instSet = new DataSource(ResourceFiles.emptyDataSetStream).getDataSet
      if (instSet.classIndex == -1)
        instSet.setClassIndex(instSet.numAttributes - 1)

      instance.setDataset(instSet)
      instSet.add(instance)
   
      val options = weka.core.Utils.splitOptions("-R 1-21,38,44,66-67,70,76-82")
      
      val remove = new Remove                         // new instance of filter
      remove setOptions options                       // set options
      remove setInputFormat instSet 
    
      val newData = Filter.useFilter(instSet, remove)
    
      val inst = newData.firstInstance
      inst.setClassMissing
      
      val pair = cls distributionForInstance inst
      ((name split '.').head, pair(1) - pair(0))
    }).toSeq.sortWith(_._2 > _._2).map(_._1)
  
}
