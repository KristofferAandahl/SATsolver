import SATsolver.Experiment.Relations.Theories

def dec (l : Lit)(t : Trail)(_ : t ¿ l): Trail :=
  ALit.decided l :: t
