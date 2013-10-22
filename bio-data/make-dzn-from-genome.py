#Make a list of .genome files into a directory of dzn files for comparison
#Input: file1.genome, file2.genome, ..., dataset (goes to ../Generate/generated-problems/dataset)
import subprocess
import glob
import sys
import random
import numpy
import matplotlib.pyplot as plt

DROP_THRESHOLD = 4 #genes mustn't drop more than or equal to this many
GENERATE_DIRECTORY_PREFIX = "generated-dzn-files/"

def removeSign(s):
    return s.replace("+","").replace("-","")

def getSign(s): #assume the sign is the first character
    return s[0]

def makeGenomeString(geneList):
    genomeString = "["
    for gene in geneList:
        genomeString += gene + ","
    genomeString = genomeString[0:-1] #delete the last character (a comma)
    genomeString += "]"
    return genomeString

#Leaves only one instance of each gene
def removeDuplicateGenes(geneList):
    genesAlreadySeen = list()
    newGeneList = list()
    for gene in geneList:
        unsignedGene = removeSign(gene)
        if (not (unsignedGene in genesAlreadySeen)):
            newGeneList.append(gene) #add the signed gene
            genesAlreadySeen.append(unsignedGene) #track unsigned genes
    return newGeneList
    
def update(ratioList, lengthList):
    print "Average compression: "+str(numpy.mean(ratioList)) +" ("+str(numpy.std(ratioList))+")"
    print "Average length: "+str(numpy.mean(lengthList)) +" ("+str(numpy.std(lengthList))+")"

#From compression output (two lines like,
#[1,-2,-3,4,5,6]
#[2,-3,1,4,-5,6]
#Make a file
def makeDZNFile(compressionOutput):
    dznFile = ""
    initial = compressionOutput.split("\n")[0]
    goal = compressionOutput.split("\n")[1]
    
    if(initial=="[]"): initial="[1]"
    if(goal=="[]"): goal="[1]"
    
    dznFile += "initialGenome="+initial+";\n"
    dznFile += "goalGenome="+goal+";\n"
    dznFile += "genomeLength="+str(len(goal.split(",")))+";\n"
    dznFile += "planLength=1;\n" #we don't use this variable any more. Here for backwards compatability
    dznFile += "inversionPenalty=1;\n"
    
    return dznFile
    
def writeDZNFile(i,j,length,contents):
    fileName = "biology-l="+str(length)+"-pl=1-i="+str(i)+"-j="+str(j)+".dzn"
    dznFile = open(GENERATE_DIRECTORY_PREFIX + dataset + "/" + fileName, 'w')
    dznFile.write(contents)
    

#ARGUMENTS
fileList = sys.argv[1:-1]
dataset = sys.argv[-1]

#Possibly make a directory for the dataset
process = subprocess.Popen(("mkdir -p generated-dzn-files/"+dataset+"/").split(), stdout=subprocess.PIPE)
output = process.communicate()[0]

#output files
problemFile = open(GENERATE_DIRECTORY_PREFIX + dataset + "/problems.csv", 'w+')
problemFile.write("index,file\n")

#pairwise compare for all files
for i in range (0,len(fileList)):
    #Append to the problem file (an index -> genome mapping)
    problemFile.write(str(i+1)+","+fileList[i]+"\n")
    
    for j in range (0,i):
        #Don't compare the same genome
        if(i==j):
            continue
            
        try:
            fileName1 = fileList[i]
            fileName2 = fileList[j]

            with open(fileName1) as file1:
                file1Lines = file1.readlines()
                
            with open(fileName2) as file2:
                file2Lines = file2.readlines()

            readingData = False
            file1Genome = list()
            file2Genome = list()

            nameNumberMap = dict() #map gene names to numbers (COX1 -> 1, for example)

            #For both files, extract the data and put it into the list
            for (genomeList, fileLines) in [(file1Genome, file1Lines), (file2Genome,file2Lines)]:
                for line in fileLines:
                    if (not readingData):
                        if(line.strip() == "<DATA>"):
                            readingData = True
                    else:
                        if(line.strip() == "</DATA>"):
                            readingData = False
                        else:
                            genomeList.append(line.strip())

            geneIndex = 1
            genome1DropCount = 0
            genome2DropCount = 0

            #Delete duplicate genes in each genome
            file1Genome = removeDuplicateGenes(file1Genome)
            file2Genome = removeDuplicateGenes(file2Genome)
            
            #Go through the first genome, assigning numbers to each gene as we come across it
            for gene in file1Genome:
                unsignedGene = removeSign(gene)
                if(unsignedGene in map(removeSign,file2Genome)): #delete genes that aren't present in both
                    if(unsignedGene not in nameNumberMap): #don't add genes more than once if there are duplicates
                        nameNumberMap[unsignedGene] = geneIndex
                    geneIndex += 1
                else:
                    genome1DropCount += 1

            #Now, go through the second genome, counting genes that we will drop
            for gene in file2Genome:
                unsignedGene = removeSign(gene)
                if(not (unsignedGene in map(removeSign,file1Genome))): #Look for genes that are not present in the dictionary
                    genome2DropCount += 1

            #Now we convert each genome
            numeric1Genome = list()
            for gene in file1Genome:
                unsignedGene = removeSign(gene)
                if(unsignedGene in nameNumberMap):
                    numericGene = getSign(gene) + str(nameNumberMap[unsignedGene])
                    numeric1Genome.append(numericGene)
                    
            numeric2Genome = list()
            for gene in file2Genome:
                unsignedGene = removeSign(gene)
                if(unsignedGene in nameNumberMap):
                    numericGene = getSign(gene) + str(nameNumberMap[unsignedGene])
                    numeric2Genome.append(numericGene)

            #Make a bash command to compress the generated genomes and see if there's any difference...
            bashCommand = "../compress/compress " + makeGenomeString(numeric1Genome) + " " + makeGenomeString(numeric2Genome)
            process = subprocess.Popen(bashCommand.split(), stdout=subprocess.PIPE)
            output = process.communicate()[0]
            
            #Find compressed length for file writing
            compressedLength = len(output.split("\n")[0].split(","))            
                        
            writeDZNFile(i+1,j+1,compressedLength,makeDZNFile(output))


            comparable = ((genome1DropCount+genome2DropCount) < DROP_THRESHOLD)
            if not comparable:
                print "ERROR: "+fileName1+" and "+fileName2+" are not comparable (unequal content)"
                continue
            else:
                #Find the compression ratio
                lengthBefore = len(numeric1Genome)
                lengthAfter = len(output.split("\n")[0].split(","))
            
        except IndexError:
            print "Parse error"
print "---Done---"
