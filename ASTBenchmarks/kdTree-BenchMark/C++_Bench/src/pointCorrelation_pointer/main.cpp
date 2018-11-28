#include "tree_unpacked.h"
#include <assert.h>
#include <chrono>

#define  TRIALS 10


//these variables are used only in test mode

int counter=0;
int counter2=0;
int counter3=0;
int nodeCount=0;
int nodeCount_test=0;


int compare_doubles (const void *a, const void *b);



void   doTest(Point * data,Tree_Node * root , float rad,int pointCount,int itterations){
    
    for(int j=0; j<min(itterations,pointCount); j++){
        
        int res;
        res=performPointCorr_IntOut( data[j], root, rad);
        counter3+=res;
        performPointCorr_OnTree(data[j], root, rad);
        Tree_Node * out= performPointCorr_TreeOut(data[j], root, rad);
        deleteTree(out);
        
    }
    cout<<counter<<","<<counter2<<","<<counter3<<endl;
    assert((counter==counter2&& counter2==counter3) && "error");
    cout<<nodeCount_test/min(itterations,pointCount)<<","<<nodeCount<<endl;
    assert(nodeCount_test/min(itterations,pointCount)==nodeCount &&"error2");
}

double evlauteRuntime(Point * data,Tree_Node * root , float rad,int pointCount,int itterations,Varient mode){
    
    //running the traversal
    double trials[TRIALS];
    
    Tree_Node * toDel[1001];
    for(int i=0; i<TRIALS; i++) {
        double time_spent=0;
        
        int amplyfiy=(pointCount<=10000)? 1000: 1;
        
        for(int j=0; j<min(itterations,pointCount); j++){
            int res;
            if(mode==Varient::intOut){
                auto t1 = std::chrono::high_resolution_clock::now();
                for(int h=0; h<amplyfiy; h++){
                    res=performPointCorr_IntOut( data[j], root, rad);
                }
                auto t2 = std::chrono::high_resolution_clock::now();
                time_spent+= std::chrono::duration_cast<std::chrono::microseconds>(t2-t1).count();
                
            }
            else if(mode==Varient::updateTree){
                auto t1 = std::chrono::high_resolution_clock::now();
                for(int h=0; h<amplyfiy; h++){
                    performPointCorr_OnTree(data[j], root, rad);
                }
                auto t2 = std::chrono::high_resolution_clock::now();
                time_spent+= std::chrono::duration_cast<std::chrono::microseconds>(t2-t1).count();
            }
            else if(mode==Varient::treeOut){
                auto t1 = std::chrono::high_resolution_clock::now();
                for(int h=0; h<amplyfiy; h++){
                    
                    toDel[h]=performPointCorr_TreeOut(data[j], root, rad);
                }
                auto t2 = std::chrono::high_resolution_clock::now();
                time_spent+= std::chrono::duration_cast<std::chrono::microseconds>(t2-t1).count();
                for(int h=0; h<amplyfiy; h++){
                    deleteTree(toDel[h]);
                }
            }
            else
                assert(false && "wrong arg 3");
        }
        
        time_spent/=1000000;
        printf("  run(%d): %lf\n", i, time_spent);
        trials[i] = time_spent;
        
    }
    
    qsort(trials, TRIALS, sizeof(double), compare_doubles);
    double avg;
    double sum=0;
    for(int i=0; i<TRIALS; i++){
        sum+=trials[i];
    }
    avg=(sum/TRIALS);
    return avg;
    
}

int main(int argc, char **argv)
{
    
    //reading inputs and building point list
    Point * data;
    float rad;
    int pointCount;
    Varient mode;
    //number of times the traversal will run and not number of TRIALS
    
    int itterations=10;
    readInput(argc,  argv, data, rad, pointCount,mode);

    
    cout<<"benchmarking mode: "<<( mode==Varient::intOut? "intout":
                                  ( mode== Varient::treeOut ? ("treeout"):
                                   ( mode== Varient::updateTree? ("updatetree"):("error!") )))<<endl;
    
    cout<<"points data of size " <<pointCount<<" are loaded "<<endl;
    
    
    //build the treed
    auto t1 = std::chrono::high_resolution_clock::now();
    Tree_Node * root=buildTree(pointCount ,  data );
    auto t2 = std::chrono::high_resolution_clock::now();
    double time_spent = std::chrono::duration_cast<std::chrono::microseconds>(t2-t1).count()/1000000;
    printf("done building, took %lf seconds\n\n", time_spent);
    
    
#ifdef TEST
    doTest(data, root, rad, pointCount, itterations);
#else
    double avg= evlauteRuntime(data, root, rad, pointCount, itterations,mode);
    
    string benchamrk_name=(mode==Varient::intOut)?     "handwritten-c-pointer-intout":
    ((mode==Varient::treeOut)?   "handwritten-c-pointer-treeout":
     "handwritten-c-pointer-updatetree");
    
    long long memoryUsage=sizeof(Tree_Node)*nodeCount;
    
    
    printf("res:[%s,%s,%d,%d,%llu,%f]\n", "kd-tree", &benchamrk_name[0], pointCount, TRIALS,  memoryUsage ,avg);
    
#endif
    
    //free memory
    delete [] data;
    deleteTree(root);
    return 0;
}

int compare_doubles (const void *a, const void *b){
    const double *da = (const double *) a;
    const double *db = (const double *) b;
    return (*da > *db) - (*da < *db);
}