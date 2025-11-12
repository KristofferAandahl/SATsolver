import SATsolver.Experiment.Relations.Theories

def propogate (t : Trail)(c : Clause)(wf : c.unit t): Trail :=
  let l := c.getunit t wf
  ALit.deduced l :: t
