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

import scala.actors.Actor._
import scala.actors.{Actor, TIMEOUT}

import javax.swing._
import java.awt.{BorderLayout, Dimension, Font}
import java.awt.event.{ActionEvent, ActionListener}

object DialogMain {
  
  def main(args : Array[String]) : Unit = new InputDialog
  
}

object InputDialog {
  
  private def asString[A](computation : => A) : String =
    captureOutput(computation) _2

  private def captureOutput[A](computation : => A) : (A, String) = {
    val buffer = new java.io.ByteArrayOutputStream
    val res = Console.withOut(buffer) (computation)
    (res, buffer.toString)
  }

  private def doLater[A](computation : => A) =
    SwingUtilities.invokeLater(new Runnable {
      def run = computation
    })
  
}

class InputDialog extends JPanel {

  import InputDialog._
  
  private def ss(c : java.awt.Component,
                 minWidth : Int, prefWidth : Int,
                 minHeight : Int, prefHeight : Int) = {
    c.setMinimumSize(new Dimension(minWidth, minHeight))
    c.setPreferredSize(new Dimension(prefWidth, prefHeight))
  }
  
  private def vScrolled(c : JComponent) =
    new JScrollPane(c,
                    javax.swing.ScrollPaneConstants.VERTICAL_SCROLLBAR_ALWAYS,
                    javax.swing.ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED)

  private def setupTextField(f : JTextArea) =
    f.setFont(new Font("Courier", Font.PLAIN, 14)) 

  //////////////////////////////////////////////////////////////////////////////
    
  private val frame = new JFrame ("Princess")
  frame add this
  ss(frame, 400, 800, 400, 800)
  
  setLayout(new BorderLayout)
  frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE)
  
  //////////////////////////////////////////////////////////////////////////////
  
  private val inputField = new JTextArea
  private val outputField = new JTextArea
  setupTextField(inputField)
  setupTextField(outputField)
  outputField setEditable false
  
  private val scrolledInputField = vScrolled(inputField)
  private val scrolledOutputField = vScrolled(outputField)

  ss(scrolledInputField, 200, 700, 150, 200)
  ss(scrolledOutputField, 200, 700, 350, 350)
  
  private val splitPane = new JSplitPane(JSplitPane.VERTICAL_SPLIT,
                                         vScrolled(outputField),
                                         vScrolled(inputField))
                                         
  add(splitPane, BorderLayout.CENTER)
    
  outputField setText asString {
    CmdlMain.printGreeting
    println
    CmdlMain.printOptions
  }
  
  inputField setText asString {
    println("\\functions {")
    println("  /* Declare constants and functions occurring in the problem")
    println("   * (implicitly universally quantified). */")
    println
    println("   int x, a, b, c;")
    println("}")
    println("\\predicates {")
    println("  /* Declare predicates occurring in the problem")
    println("   * (implicitly universally quantified)")
    println("   *")
    println("   * e.g., divides(int, int);  */")
    println("}")
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
    println
    println("/*")
    println("// Array example")
    println("")
    println("\\functions {")
    println("  int x, y, z;")
    println("  int ar;")
    println("  \\partial int select(int, int);")
    println("  \\partial int store(int, int, int);")
    println("}")
    println
    println("\\problem {")
    println("// Array axioms")
    println("        \\forall int ar, ind, val;")
    println("             {select(store(ar, ind, val), ind)}")
    println("             select(store(ar, ind, val), ind) = val")
    println("->")
    println("        \\forall int ar, ind1, ind2, val;")
    println("             {select(store(ar, ind1, val), ind2)}")
    println("             (ind1 != ind2 ->")
    println("              select(store(ar, ind1, val), ind2) = select(ar, ind2))")
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
    println("*/")
  }
  
  //////////////////////////////////////////////////////////////////////////////

  private val buttonPanel = new JPanel
  buttonPanel.setLayout(new BorderLayout)
  add(buttonPanel, BorderLayout.SOUTH)

  private val optionLabel = new JLabel("Options: ")
  buttonPanel.add(optionLabel, BorderLayout.WEST)
  
  private val optionField = new JTextField
  buttonPanel.add(optionField, BorderLayout.CENTER)
  
  private val toolTip = asString {
    println("<html><pre>")
    CmdlMain.printOptions
    println("</pre></html>")
  }

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
  buttonPanel.add(goButton, BorderLayout.EAST)
  goButton setToolTipText toolTip

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
        goButton setText "Go!"
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

  frame.pack
  splitPane setDividerLocation 0.35
  frame setVisible true
  
}
