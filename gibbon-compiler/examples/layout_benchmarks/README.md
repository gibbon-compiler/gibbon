This is a collection of some benchmarks that show how layout affects performance.
In particular this set of benchmarks shows how the position of different fields in the data layout could potentially affect performance. 
The file Adts.hs contains the definitions of all the abstract data types and some other accompanying functions.
The file Strings.hs contains the definition of the data type String which is a Cons Int list. 
The file Tags.hs contains the definition of the data type Tags which is also a Cons Int list. 
the file Contents.hs contains the definition of the data type Content which can be an Image string or Text string. 

3 different senarios: 

1.) Counting the length of two different Adts (Abstract data types) 
    CA (Content) (Adts) -> Content is serialzed first before we serialize the next Adt. 
    AC (Adts) (Content) -> The next Adt is serialized first before we serialize any of the Content. 
    
    Here the fuction simply counts the length of the Adt given these 2 different data layouts. 
    
    Performance disscussion... 
    
    Here the CA data layout results in slower performance that the AC layout. 
    This is because the CA layout inserts pointers to the next Adt so that it can quickly skip over the Content and to count the length of the Adt. This causes the program to chases pointes to get to the end of the list. 
    On the other hand, the AC list does not have these pointers and simply traverses the Next directly since they are contigous in memory. This way it does not have to chase pointes and the program exits when it sees Nil without having to deal with the content. 
    
    
2.) Processing the content. Comparing the performance of CA vs AC

    TODO: add some discussion here... 


3.) Processing tags when the Abstract data type has 3 fields, Tags, Content and Next Adt. 

    Here we test all the 6 permutations of the layout but specifically discuss the performance of the TAC and CAT layouts. 
    TAC -> Tags, Adt next and then Content is serialized. 
    CAT -> Content, next Adt and then Tags are serialized. 
    
    TAC is faster than CAT. The function adds a set value to all the tags (emulating a traversal over all the tags)
    TODO: Add more explanation here...
    
    Performance testing using PAPI, we measure the L2, L3 cache misses, number of Instructions and Cycles. 
    
    The test makes TAC and CAT abstract data layout of size 10,000 cells. 
    Each cell has a list of 10 tags and Content of size 2000 characters. (in the form of Text string)   
    
    TAC
    L2 Cache Misses : 1691512
    L3 Cache Misses : 1077805
    Instructions : 35909014
    Total Cycles : 19966967
    TIMES: [0.007887]
    ITERS: 1
    SIZE: 1
    BATCHTIME: 7.886575e-03
    SELFTIMED: 7.886575e-03
    '#()    
    
    CAT
    L2 Cache Misses : 2188086
    L3 Cache Misses : 1570776
    Instructions : 79688633
    Total Cycles : 82205312
    TIMES: [0.048111]
    ITERS: 1
    SIZE: 1
    BATCHTIME: 4.811104e-02
    SELFTIMED: 4.811104e-02
    '#()
    
    TAC has less L2 and L3 cache misses, lesser instructions and cycles and consequently a lower runtime. 

    Speedup ~ 6x.
    
