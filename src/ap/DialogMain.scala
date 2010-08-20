/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

package ap;

import ap.parameters.{GlobalSettings, Param}
import ap.util.CmdlParser

import scala.collection.mutable.ArrayBuffer
import scala.actors.Actor._
import scala.actors.{Actor, TIMEOUT}

import javax.swing._
import java.awt.{BorderLayout, FlowLayout, Dimension, Font, Color}
import java.awt.event.{ActionEvent, ActionListener}

object DialogMain {
  
  def main(args : Array[String]) : Unit = new InputDialog
  
}

object DialogUtil {
  
  def asString[A](computation : => A) : String =
    captureOutput(computation) _2

  def captureOutput[A](computation : => A) : (A, String) = {
    val buffer = new java.io.ByteArrayOutputStream
    val res = Console.withOut(buffer) (computation)
    (res, buffer.toString)
  }

  def doLater[A](computation : => A) =
    SwingUtilities.invokeLater(new Runnable {
      def run = computation
    })
  
  def ss(c : java.awt.Component,
         minWidth : Int, prefWidth : Int,
         minHeight : Int, prefHeight : Int) = {
    c.setMinimumSize(new Dimension(minWidth, minHeight))
    c.setPreferredSize(new Dimension(prefWidth, prefHeight))
  }
  
  def vScrolled(c : JComponent) =
    new JScrollPane(c,
                    javax.swing.ScrollPaneConstants.VERTICAL_SCROLLBAR_ALWAYS,
                    javax.swing.ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED)

  def setupTextField(f : JTextArea) =
    f.setFont(new Font("Courier", Font.PLAIN, 14)) 

}

////////////////////////////////////////////////////////////////////////////////

class InputDialog extends JPanel {

  import DialogUtil._
  
  //////////////////////////////////////////////////////////////////////////////

  private val frame = new JFrame ("Princess")
  frame add this
  ss(frame, 400, 800, 400, 800)
  
  setLayout(new BorderLayout)
  frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE)
  
  //////////////////////////////////////////////////////////////////////////////

  private val tabbedPane = new JTabbedPane (SwingConstants.BOTTOM)
  add(tabbedPane)

  private def newPanel : PrincessPanel =
    new PrincessPanel {
      def setRunning = {
        val i = tabbedPane.indexOfComponent(this)
        tabbedPane.setBackgroundAt(i, Color.red)
        tabbedPane.setToolTipTextAt(i, "Solving ...")
      }
      def setFinished = {
        val i = tabbedPane.indexOfComponent(this)
        tabbedPane.setBackgroundAt(i, null)
        tabbedPane.setToolTipTextAt(i, null)
      }
      def newTab = {
        val tab = newPanel
        createdTabs = createdTabs + 1
        tabbedPane.addTab("Problem " + createdTabs, tab)
        tab.inputField setText asString {
          println("\\universalConstants {")
          println("  /* Declare universally quantified constants of the problem */")
          println("  ")
          println("}")
          println
          println("\\existentialConstants {")
          println("  /* Declare existentially quantified constants of the problem */")
          println("  ")
          println("}")
          println
          println("\\functions {")
          println("  /* Declare constants and functions occurring in the problem")
          println("   * (implicitly universally quantified).")
          println("   * The keyword \"\\partial\" can be used to define functions without totality axiom,")
          println("   * while \"\\relational\" can be used to define \"functions\" without functionality axiom. */")
          println("  ")
          println("}")
          println
          println("\\predicates {")
          println("  /* Declare predicates occurring in the problem")
          println("   * (implicitly universally quantified) */  ")
          println("  ")
          println("}")
          println
          println("\\problem {")
          println("  /* Problem to be proven. The implicit quantification is:")
          println("   *    \\forall <universalConstants>;")
          println("   *      \\exists <existentialConstants>;")
          println("   *        \\forall <functions/predicates>; ... */")
          println
          println("  true")
          println("}")
        }
        tab.inputField setCaretPosition 0
        tabbedPane setSelectedIndex (tabbedPane.getTabCount - 1)
      }
      def closeTab = {
        if (tabbedPane.getTabCount == 1)
          // make sure that there is at least one tab left
          newTab
        tabbedPane remove this
      }
    }
  
  private var createdTabs = 3
  
  {
  val tab = newPanel
  tabbedPane.addTab("Arithmetic example", tab)
  tab.inputField setText asString {
    println("/**")
    println(" * Example:")
    println(" * Problem in Presburger arithmetic with uninterpreted predicates")
    println(" */")
    println
    println("\\existentialConstants {")
    println("  /* Declare existentially quantified constants of the problem */")
    println
    println("  int A;")
    println("}")
    println
    println("\\predicates {")
    println("  /* Declare predicates occurring in the problem */  ")
    println
    println("  divides(int, int);")
    println("}")
    println
    println("\\problem {")
    println("  /* Problem to be proven. The implicit quantification is:")
    println("   *    \\exists <existentialConstants>; \\forall <predicates>; ... */")
    println
    println("     \\forall int x; divides(x, x)")
    println("  -> \\forall int x, y; (divides(x, y) -> divides(x, y+x) & divides(x, y-x))")
    println("  ->")
    println("     divides(A, 42) & divides(A, 49) & A > 1")
    println("}")
  }
  }
  {
  val tab = newPanel
  tabbedPane.addTab("Arithmetic interpolation example", tab)
  tab.inputField setText asString {
    println("/**")
    println(" * Example:")
    println(" * Craig interpolation problem in Presburger arithmetic")
    println(" */")
    println
    println("\\functions {")
    println("   int x, a, b, c;")
    println("}")
    println
    println("\\problem {")
    println("  /* Problem to be proven and interpolated */")
    println
    println("  \\part[cond]          (a-2*x = 0 & -a <= 0) &")
    println("  \\part[stmt1]         (2*b - a <=0 & -2*b + a -1 <=0) &")
    println("  \\part[stmt2]         c-3*b-1=0")
    println("                       ->")
    println("  \\part[assert]        c > a")
    println("}")
    println
    println("/* Interpolation specification */")
    println("\\interpolant {cond; stmt1, stmt2, assert}")
    println("\\interpolant {cond, stmt1; stmt2, assert}")
    println("\\interpolant {cond, stmt1, stmt2; assert}")
  }
  }
  {
  val tab = newPanel
  tabbedPane.addTab("Array interpolation example", tab)
  tab.inputField setText asString {
    println("/**")
    println(" * Example:")
    println(" * Craig interpolation problem in the theory of arrays")
    println(" */")
    println
    println("\\functions {")
    println("  int x, y, z, ar;")
    println("  \\partial int select(int, int);")
    println("  \\partial int store(int, int, int);")
    println("}")
    println
    println("\\problem {")
    println("// Array axioms")
    println("  \\forall int ar, ind, val; {select(store(ar, ind, val), ind)}")
    println("    select(store(ar, ind, val), ind) = val")
    println("->")
    println("  \\forall int ar, ind1, ind2, val; {select(store(ar, ind1, val), ind2)}")
    println("    (ind1 != ind2 -> select(store(ar, ind1, val), ind2) = select(ar, ind2))")
    println("->")
    println
    println("  \\part[p0] (store(0, x, 1) = ar)")
    println("->")
    println("  \\part[p1] (select(ar, y) >= select(ar, x))")
    println("->")
    println("  \\part[p2] (z = select(ar, y)+1)")
    println("->")
    println("  \\part[p3] (z < 0)")
    println("->")
    println("  false")
    println("}")
    println
    println("\\interpolant {p0, p1; p2, p3}")
  }
  }
  
  tabbedPane setSelectedIndex 0
  
  //////////////////////////////////////////////////////////////////////////////

  frame.pack
  frame setVisible true
  
}

////////////////////////////////////////////////////////////////////////////////

abstract class PrincessPanel extends JPanel {

  import DialogUtil._

  def setRunning : Unit
  def setFinished : Unit
  def closeTab : Unit
  def newTab : Unit
  
  //////////////////////////////////////////////////////////////////////////////
  
  setLayout(new BorderLayout)

  val inputField = new JTextArea
  val outputField = new JTextArea
  setupTextField(inputField)
  setupTextField(outputField)
  outputField setEditable false
  
  private val scrolledInputField = vScrolled(inputField)
  private val scrolledOutputField = vScrolled(outputField)

  ss(scrolledInputField, 200, 700, 0, 350)
  ss(scrolledOutputField, 200, 700, 0, 250)
  
  private val splitPane = new JSplitPane(JSplitPane.VERTICAL_SPLIT,
                                         scrolledOutputField, scrolledInputField)
                                         
  add(splitPane, BorderLayout.CENTER)
    
  outputField setText asString {
    CmdlMain.printGreeting
//    println
//    CmdlMain.printOptions
  }

  //////////////////////////////////////////////////////////////////////////////

  private val controlPanel = new JPanel
  controlPanel.setLayout(new BorderLayout)
  add(controlPanel, BorderLayout.SOUTH)

  private val leftPanel = new JPanel
  leftPanel setLayout (new FlowLayout (FlowLayout.LEADING, 2, 1))
  controlPanel.add(leftPanel, BorderLayout.WEST)
  
  private val newTabButton = new JButton("New tab")
  leftPanel.add(newTabButton)

  newTabButton addActionListener (new ActionListener {
    def actionPerformed(e : ActionEvent) = newTab
  })

  private val closeTabButton = new JButton("Close tab")
  leftPanel.add(closeTabButton)

  closeTabButton addActionListener (new ActionListener {
    def actionPerformed(e : ActionEvent) = {
      if (currentProver != null)
        currentProver ! "stop"
      closeTab
    }
  })

  leftPanel add Box.createRigidArea(new Dimension (8, 0))
  private val optionLabel = new JLabel("Options: ")
  leftPanel.add(optionLabel)
  
  private val optionField = new JTextField
  controlPanel.add(optionField, BorderLayout.CENTER)
  
  private val toolTip = asString {
    println("<html><pre>")
    CmdlMain.printOptions
    println("</pre></html>")
  }

  //////////////////////////////////////////////////////////////////////////////

  optionLabel setToolTipText toolTip
  optionField setToolTipText toolTip

  optionField addActionListener (new ActionListener {
    def actionPerformed(e : ActionEvent) = {
      if (currentProver == null)
        startProver
      }
    })
  
  //////////////////////////////////////////////////////////////////////////////

  private val goButton = new JButton("Go!")
  goButton setForeground Color.BLUE
  controlPanel.add(goButton, BorderLayout.EAST)

  private var currentProver : Actor = null
  
  goButton addActionListener (new ActionListener {
    def actionPerformed(e : ActionEvent) = {
      if (currentProver == null) {
        startProver
      } else {
        currentProver ! "stop"
        goButton setEnabled false
        goButton setText "Stopping ..."
      }
    }
  })

  private def startProver : Unit = {
    val reader = new java.io.StringReader(inputField.getText)
    
    val settings = try {
      GlobalSettings.fromArguments(optionField.getText.split(' '),
                                   GlobalSettings.DEFAULT) _1
    } catch {
      case e : CmdlParser.UnknownArgumentException => {
        outputField setText asString {
          println(e.getMessage)
          println
          CmdlMain.printOptions
        }
        outputField setCaretPosition 0
        return
      }
    }

    outputField setText ""
    goButton setText "STOP"
    goButton setForeground Color.RED
    setRunning

    val proverOutputStream = new java.io.PipedOutputStream
    val logInputStream = new java.io.PipedInputStream(proverOutputStream)
    
    // start one thread for proving the problem
    currentProver = actor {
      var stop : Boolean = false
      Console.withOut(proverOutputStream) {
        CmdlMain.proveProblems(settings, List(("", reader)), {
          receiveWithin(0) { case TIMEOUT => // nothing
                             case _ => stop = true }
          stop
        } )
      }
      proverOutputStream.close
      doLater {
        currentProver = null
        goButton setEnabled true
        goButton setForeground Color.BLUE
        goButton setText "Go!"
        setFinished
      }
    }
    
    // and another one for logging the output
    actor {
      val buf = new StringBuffer
      var c = logInputStream.read
      while (c != -1) {
        buf append c.toChar
        if (logInputStream.available == 0) {
          // otherwise, read all available data and
          // display it at once
          val str = buf.toString
          buf.delete(0, buf.length)
            doLater {
              outputField append str
            }
        }
        c = logInputStream.read
      }
    }    
  }
  
  //////////////////////////////////////////////////////////////////////////////

  splitPane setContinuousLayout true
  
}