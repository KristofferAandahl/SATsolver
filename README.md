# SATsolver
This repository contains all code files for my master thesis. To run the code build the project using
```
lake build
```
While standing in the project folder.
To run the project use:
```
.\.lake\build\bin\SATsolverExe.exe <folder containing sat files> <number of files to run (optional)>
```
The solver takes DIMACS formatted files and are tested using problems from University of British Columbias SATLIB. https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html.

To run the same files using CaDiCaL a cleaner script and a run script has been supplied. This run on linux and require that CaDiCaL is installed. Manual updating of folder name and file amount is required 
