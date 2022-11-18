INCLUDE=-I/local/scratch/a/singhav/Applications/src/uthash-2.3.0/include/

#rm layout1
#rm layout2 
#rm layout3 
#rm layout4 
#rm layout5 
#rm layout6 
#rm layout7 
#rm layout8

gibbon --packed --no-gc --toC layout1TagSearch.hs; gcc $INCLUDE -O3 layout1TagSearch.c  -o layout1

gibbon --packed --no-gc --toC layout2TagSearch.hs; gcc $INCLUDE -O3 layout2TagSearch.c  -o layout2

gibbon --packed --no-gc --toC layout3TagSearch.hs; gcc $INCLUDE -O3 layout3TagSearch.c  -o layout3 

gibbon --packed --no-gc --toC layout4TagSearch.hs; gcc $INCLUDE -O3 layout4TagSearch.c  -o layout4 

gibbon --packed --no-gc --toC layout5TagSearch.hs; gcc $INCLUDE -O3 layout5TagSearch.c  -o layout5 

gibbon --packed --no-gc --toC layout6TagSearch.hs; gcc $INCLUDE -O3 layout6TagSearch.c  -o layout6 

gibbon --packed --no-gc --toC layout7TagSearch.hs; gcc $INCLUDE -O3 layout7TagSearch.c  -o layout7 

gibbon --packed --no-gc --toC layout8TagSearch.hs; gcc $INCLUDE -O3 layout8TagSearch.c  -o layout8

for i in {1..8}
do
   
   echo "Start experiment for layout${i}"
   echo    
   #for j in {1..10}
   #do
   #	 echo  
   ./layout${i} --RUN 9 
   #echo
   #done 
   echo "Done with layout${i}"
   echo 
done 


#./layout1 --RUN 3
#./layout2 --RUN 3 
#./layout3 --RUN 3
#./layout4 --RUN 3
#./layout5 --RUN 3
#./layout6 --RUN 3
#./layout7 --RUN 3
#./layout8 --RUN 3

#rm layout1
#rm layout2 
#rm layout3 
#rm layout4 
#rm layout5 
#rm layout6 
#rm layout7 
#rm layout8
