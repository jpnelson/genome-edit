#!/bin/bash

echo "#####################"
echo "#     ITT solver    #"
echo "#####################"

model=$1
string1=$2
string2=$3

echo ""
echo "#Using "$model" model, with"
echo "genome #1 =" $string1
echo "genome #2 = "$string2
model_file=genome-$model.mzn
minizinc_options=" -b lazyfd"

#Decide if we're going to pipe the output into relationalPrint
pipeOutput="cat" #just cat the output for the positional model
if [[ $model = "relational" ]]
then
    pipeOutput="./relational-print/relationalPrint"
fi

#Make the DZN file
touch tmp.dzn
echo "initialGenome="$string1";"  > tmp.dzn
echo "goalGenome="$string2";"  >> tmp.dzn
commas=`echo "$string1" | grep -o "," | wc -l`
length=`expr $commas + 1`
echo "genomeLength="$length";"  >> tmp.dzn
echo "planLength=1;"  >> tmp.dzn #this is not used any more, but the models expect this variable for backwards comaptability
echo "inversionPenalty=1;" >> tmp.dzn
echo "costCap="$length";" >> tmp.dzn

echo "#Using cost cap of "$length", use baobab or another calculated IO distance for a tighter bound"
echo "-------------------"
echo ""


#Do the solving
time_start=`date +%s`
minizinc "$model_file" $minizinc_options tmp.dzn 2>/dev/null | $pipeOutput #don't output warning messages
time_end=`date +%s`

echo "-------"
echo ""
echo "Completed in "$((time_end-time_start))" second(s)"

rm tmp.dzn
