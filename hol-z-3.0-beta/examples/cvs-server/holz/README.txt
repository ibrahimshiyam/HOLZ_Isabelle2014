This directory 
--------------

(holz/examples/zeta/cvs-server/holz)
...contains the proof files for the CVS Server Case Study. After a successful 
make operation on the top level of HOL-Z, the *.holz files of the CVS 
Server Model appear in this directory. They can be imported using the 
command 'use_holz'. 

short Instructions:
-------------------

- decide if you want to view
	- Consistency Proofs (Definedness, Deadlockfreedom)
	- Security Proofs (Write, Read)

- modify the file zetarc.template in the directory cvs-server 
 (one level above): 
	- for Consistency use only the lines:

		plugin HOLZAdaptor
		load arch.tex
		holz -u LTX:SysArchConsistency#arch
		quit

	(and comment the rest out using #)

	- for Security use only the lines:

                plugin HOLZAdaptor
                load arch.tex
		holz -u LTX:SysArchSec#arch
                quit

	(and comment the rest out using #)

- enter 'make' at the command line in the directory above
  (holz/examples/zeta/cvs-server)

- read the desired theory (e.g. use_holz"SysArchConsistency" or
  use_holz"SysArchSec" from a isabelle holz - shell)

For more details on the theories, view the files SysArchConsistency.ML or 
SysArchSec.ML.


Concerning Consistency
-----------------------

Lemma Libraries for the corresponding Zsections of the Z-Specification can 
be found in the files:

Basics.ML
AbstractState.ML 
FileSystem.ML
CVSServer.ML


The proofs for the definedness and deadlockfree consistency conditions are 
in the files:

AbstractStateCons.ML
AbsOperationsCons.ML
FileSystemCons.ML
CVSServerCons.ML

To load all the Proofs avoiding dependency conflicts simply type:

use "SysArchConsistency";
(The file SysArchConsistency imports the proofs in the right order)


The proofs for the Refinement Condition are in the file:

Refinement.ML


Concerning Security
--------------------

The file 

pruningTactics.ML 

contains a few Tactics which allow pruning of 
assumptions. It still has experimental status.

Proofs for the Security Properties are in the files
listed in the file 

Env.ML

Several files which serve as lemma libraries for the most schemas and
axiomatic definition environments exist. The file

SimpleAbsOpsImpls.ML

e.g. contains a set of simple implications of schemata.

The file abs_writeSec.ML contains a full proof of the AWriteSec
property. It uses abs_Passwd_zrtrancl.ML and LoginAknows.ML,
SimpleAbsOpsImpls.ML as the main contributing sources.



----------
