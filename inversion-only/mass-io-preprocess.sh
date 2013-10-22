#!/bin/bash
#Pre processes dzn files by adding baobab costs to them

dzn_directory=$1

for dzn_file in `ls -tr $dzn_directory` #sort by reverse creation date to do easy ones first
do
    echo "Preprocessing file "$dzn_file
    #FILENAME
    
    #Convert dzn file to sequence for baobab
    sequence=$(cat $dzn_directory$dzn_file | grep "initialGenome" | tr -d "initialGenome=[" | tr -d "];") #strip it to just the sequence
    targetSequence=$(cat $dzn_directory$dzn_file | grep "goalGenome" | tr -d "goalGenome=[" | tr -d "];") #strip it to just the sequence
    
    #COST
    output=$(java -classpath baobab-luna.jar baobab.exec.permutation.sort -l F -o $sequence -t $targetSequence)
    plancost=$(echo "$output" | grep -m 1 "Reversal distance: " | tr -d '\n' | tr -d "Reversal distance: ")
    
    #Append the baobab result to the dzn file
    echo "costCap="$plancost";" >> $dzn_directory$dzn_file
done
