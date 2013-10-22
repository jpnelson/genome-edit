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

std::string convertInt(int number)
{
   std::stringstream ss;//create a stringstream
   ss << number;//add number to the stream
   return ss.str();//return a string with the contents of the stream
}

std::string makeVectorString(std::vector<int> vec){
    std::string outputString = "";
    for(int i = 0; i < vec.size(); i++){
        outputString += convertInt(vec[i]);
        if(i+1 < vec.size()){
            outputString += ", ";
        }
    }
    return outputString;
}

//Converts a relational encoded genome vector to a positionally encoded one by following the left neighbour array
std::string positionalEncode(std::vector<int> relational, std::vector<int> signs){
    std::vector<int> positional;
    positional.push_back(1 * signs[0]); //arbitrarily choose the start index to display. Don't forget the sign (might be negative)
    
    while(positional.size() < relational.size()){
        int lastFollowed = std::abs(positional.front()); //we always insert things at the beginning. Only interested in the gene content we just added, not the sign
        int leftNeighbour = relational[lastFollowed-1];
        
        //put at the start, as we are working from back to front
        //Also insert the sign
        positional.insert(positional.begin(),leftNeighbour * signs[leftNeighbour-1]); 
    }
    
   return makeVectorString(positional);
}

std::vector<int> makeLineArray(std::string line){
    //Go through and split up the line with commas
    std::vector<std::string> lineSplit = split(line,',');
    std::vector<int> parsedArray;
    for(int i = 0; i < lineSplit.size(); i++){
        //Go through and extract just the numbers and put them in an array
        std::string noJunkStart = split(lineSplit[i],'[')[split(lineSplit[i],'[').size()-1];
        std::string noBrackets = split(noJunkStart,']')[split(noJunkStart,']').size()-1];
        noBrackets.erase( remove( noBrackets.begin(), noBrackets.end(), ' ' ), noBrackets.end() );
        std::string reformatted = noBrackets; //remove spaces finally
        
        parsedArray.push_back(atoi(reformatted.c_str())); //we make an array of integers for conversion
    }
    
    return parsedArray;
}



int main(int argc, char **argv) {
    //The pipe
    std::string lineInput;
    
    //The final lines to rewrite as positional encoding
    std::vector<std::string> reformattedLines;
    
    //Parsed info
    std::vector<std::vector<int> > geneSigns;
    std::vector<std::vector<int> > relationalEncoding;
    while (getline(std::cin,lineInput)) {
        
        if(lineInput.find("Signs t=") != -1){
            //Get the signs too
            std::vector<int> parsedArray = makeLineArray(lineInput);
            geneSigns.push_back(parsedArray);
        }
        if(lineInput.find("leftNeighbour t=") != -1){
            //we have a result we want to reformat
            std::vector<int> parsedArray = makeLineArray(lineInput);
            relationalEncoding.push_back(parsedArray);
        }
        
        std::cout << lineInput << "\n";
    }
    //We need to combine the sign and number data to output the positional encoding
    for(int i = 0; i < relationalEncoding.size(); i++){
        reformattedLines.push_back(positionalEncode(relationalEncoding[i],geneSigns[i]));
    }
    
    //Now at the end, output our reformatted lines
    std::cout << "Positional encoding::\n";
    for(int i = 0; i < reformattedLines.size(); i++){
        std::cout << "State t=" << convertInt(i+1) << ": " << "[" << reformattedLines[i] << "]\n";
    }
    return 0;
}
