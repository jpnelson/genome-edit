#genome-edit README

Joshua Nelson, 2013

This folder contains the basic framework required to calculate ITT genome edit distances with constraint satisfaction.

It is assumed that MiniZinc has been installed, and is avialable from your PATH variable. To check, type

    $ minizinc --version
    >G12 MiniZinc evaluation driver, version 1.6.0
    >Copyright (C) 2011-2012 The University of Melbourne and NICTA

If you receive the output above, the scripts will work as intended.

The file structure is
* bio-data/  -Contains scraped mitochondrial genomes from the NCBI database, and a script to convert this into .dzn files for the MiniZinc solver
    
* compress/  -Contains code, and a binary file, for compressing a circular genome.
    
* genome-edit-distance/  -Contains genome-positional.mzn, genome-relational.mzn; the MiniZinc model files used for computation, and a shell script for these, itt-edit-distance.sh, which can run either of these models on a sequence directly. 
Also contains a program to convert relational model output to positional output for better interpretation of plans and results.
                              
* inversion-only/  -Contains baobab-lunar.jar, the inversion-only solver used, and a script that uses this to pre-process .dzn files with a "costCap=N;" parameter, which provides the MiniZinc solvers with an upper bound on plan cost
