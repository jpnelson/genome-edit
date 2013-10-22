#include <iostream>
#include <vector>
#include <list>
#include <cmath>
#include <algorithm>
#include <cstdlib>
#include <assert.h>
#include <sys/time.h>
#include <string>
#include <sstream>
#include <limits.h>

//string split function
std::vector<std::string> &split(const std::string &s, char delim, std::vector<std::string> &elems) {
    std::stringstream ss(s);
    std::string item;
    while (std::getline(ss, item, delim)) {
        elems.push_back(item);
    }
    return elems;
}

std::vector<std::string> split(const std::string &s, char delim) {
    std::vector<std::string> elems;
    split(s, delim, elems);
    return elems;
}

//with a genome, renumber from [1,8,-3] -> [1,3,-2]
std::vector<int> renumberArray(std::vector<int> genome){
    std::vector<int> renumberedGenome = genome;
    std::vector<int> indicesAdded = std::vector<int>(); //keep track of the indices we've added so we don't keep adding the same ones
    for(int currentNumber = 1; currentNumber <= (genome.size()); currentNumber++){
        int minValue = INT_MAX; //absolute value. Going to be replaced in first iteration 
        int minIndex = -1;
        
        
        //Find the gene to replace at this step
        for(int g = 0; g < genome.size(); g++){
            //Don't bother with indices we've added already
            bool alreadyAdded = false;
            for(int i = 0; i < indicesAdded.size(); i++){
                if(indicesAdded[i] == g){
                    alreadyAdded = true;
                    break;
                }
            }
            if(alreadyAdded) continue;
            
            
            int thisAbsoluteValue = std::abs(genome[g]);
            if(thisAbsoluteValue < minValue){
                minValue = thisAbsoluteValue;
                minIndex = g;
            }
        }
        
        
        int geneSign = genome[minIndex] > 0 ? 1 : -1;
        renumberedGenome[minIndex] = currentNumber * geneSign;
        indicesAdded.push_back(minIndex);
    }
    
    return renumberedGenome;
}

//Convert a string to a genome vector
std::vector<int> convert(std::string genomeString){
	//Remove square brackets
	genomeString = genomeString.substr(1,genomeString.length()-2);
	//Split on commas
	std::vector<std::string> stringVectorGenome = split(genomeString,',');
	
	//Convert strings to integers
	std::vector<int> convertedGenome;
	for(int i = 0; i < stringVectorGenome.size(); i++) {
    	convertedGenome.push_back(atoi(stringVectorGenome[i].c_str()));
	}
	return convertedGenome;
}



//Checks to see if (gene1,gene2) is a pair in genome. Returns -1 if found backwards, 1 if found forwards, 0 if not found 
int checkPair(std::vector<int> genome, int gene1, int gene2){
	int length = genome.size();
	for(int i = 0; i < length; i++){
		if ((genome[i] == gene1) && (genome[(i+1) % length] == gene2)){ //check forwards
			return 1;
		}
		else if ((genome[i] == -gene2) && (genome[(i+1) % length] == -gene1)){ //check backwards
			return -1;
		}
	}
	
	return 0; //couldn't find anything
}

void printVector(std::vector<int> v){
	std::cout << "[";
	for(int i = 0; i < v.size(); i++){
		std::cout << v[i];
		if(i < v.size()-1){
			std::cout << ",";
		}
	}
	std::cout << "]\n";
}

//Loop through the genomes, and find a pair to compress. This will be repeated until no more pairs can be compressed.
//Returns whether or not compression took place
bool compressPairs(std::vector<int> &g1, std::vector<int> &g2){
	int length = g1.size();
	if(length==0){
		return false; //at this length, we're done
	}
	assert(length == g2.size());
	
	
	//Loop through g1, and check if each is a pair in g2.
	for(int i = 0; i < length; i++){
		int indexFirst = i;
		int indexSecond = (i+1) % length;
		int pairFirst = g1[indexFirst];
		int pairSecond = g1[indexSecond];
		int pairStatus = checkPair(g2,pairFirst,pairSecond);
		
		if(pairStatus != 0){ //we've found something to compress
			int newGene = std::min(std::abs(pairFirst),std::abs(pairSecond));
			//Compress in g1
			//First gets the new value (which is the abs. min) 
			g1[indexFirst] = newGene; //g1 always gets the positive newGene. Possibly negate the gene in g2
			//Second gets deleted
			g1.erase(g1.begin() + indexSecond);
			
			//Compress in g2
			//Look for the index again in g2 (it doesn't get passed with checkPair)
			for(int j = 0; j < length; j++){
				if(g2[j]==pairFirst || g2[j]==-pairFirst){ //Look for the pair to compress in g2
					g2[j] = pairStatus * newGene; //we might want to change sign if it was found backwards
					
					int indexToErase = (j+pairStatus) % length; //delete in the correct direction from j, according to pairStatus
					if(indexToErase < 0) indexToErase += length; //% does not act like mod in c++
					
					g2.erase(g2.begin() + indexToErase); 


				}
			}
			return true; //could keep going, but we make things simple and only do one compression per call
		}
	}
}




int main (int argc, char *argv[])
{

	std::string genome1String = argv[1];
	std::string genome2String = argv[2];
	std::vector<int> genome1 = convert(genome1String);
	std::vector<int> genome2 = convert(genome2String);
	

	bool keepCompressing = true;
	while(keepCompressing){
		keepCompressing = compressPairs(genome1,genome2);
	}
	printVector(renumberArray(genome1));
    printVector(renumberArray(genome2));
	
	return 0;
}


