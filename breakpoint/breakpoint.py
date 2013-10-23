#!/usr/bin/python
#Given two sequences, computes the breakpoint distance between them

import sys
import math

#Make a genome out of a formatted array string [1,2,-3,4]
def parseGenome(s):
    return map(int,s.split('[')[-1].split(']')[0].split(','))

def genesAdjacentIn(gene1, gene2, genome):
    
    gene1Location = map(abs,genome).index(abs(gene1))
    gene2Location = map(abs,genome).index(abs(gene2))
    
    #Check to see if gene1 is negated - if so, the pair must appear in reverse
    appearsReversed = False
    if genome[gene1Location] == -gene1:
        appearsReversed = True
    else:
        appearsReversed = False
    
    pairIsAdjacent = True
    if(appearsReversed): #we expect gene2 to precede gene1. It must also have a negated sign
        pairIsAdjacent = ((genome[gene2Location] == -gene2) and (gene2Location == (gene1Location-1) % len(genome)))
    else: #we expect gene2 to succeed gene1. It must have the same sign
        pairIsAdjacent = ((genome[gene2Location] == gene2) and (gene2Location == (gene1Location+1) % len(genome)))
    
    return pairIsAdjacent
    
    
    

def calculateBreakpoints(genome1,genome2):
    breakpoints = 0
    
    for firstGeneIndex in range(0,len(genome1)):
        secondGeneIndex = (firstGeneIndex + 1) % len(genome1) #secondGeneIndex is the one afterwards (remembering circular genome)
        
        #Find the genes at the indices
        gene1 = genome1[firstGeneIndex]
        gene2 = genome1[secondGeneIndex]
        
        if not genesAdjacentIn(gene1, gene2, genome2):
            breakpoints += 1
        
    return breakpoints

#takes a dzn file name, and returns lists containing the     
def sequencesFromDZN(fileName):
    #The output
    initialGenome = list()
    goalGenome = list()
    
    with open(fileName) as f:
        for line in f.readlines():
            if "initialGenome" in line:
                initialGenome = parseGenome(line.strip().replace("initialGenome=","").replace(";","")) #reformat the line to extract [1,2,3,4] format
            if "goalGenome" in line:
                goalGenome = parseGenome(line.strip().replace("goalGenome=","").replace(";","")) #reformat the line to extract [1,2,3,4] format
                
    return (initialGenome, goalGenome)

#ARGUMENTS
initial = parseGenome(sys.argv[1])
goal = parseGenome(sys.argv[2])

print calculateBreakpoints(initial,goal)

