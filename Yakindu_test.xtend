package hu.bme.mit.inf.dslreasoner.application.FAMTest

import hu.bme.mit.inf.dslreasoner.application.execution.StandaloneScriptExecutor

class Yakindu_test {	
	def static void main(String[] args) {
		val msg = StandaloneScriptExecutor.executeScript("configs/generation_2.vsconfig")
		println(msg)
	}
}