#include "tree_packed.h"
#include <assert.h>
#include <chrono>

#define  TRIALS 10

int counter=0;
int counter2=0;
int counter3=0;
int nodeCount=0;
int nodeCount_INNER=0;
int compare_doubles (const void *a, const void *b);

void   doTest(Point * data,char * root_noIndirection, char * root_withIndirection , float rad,int pointCount,int itterations){
    
    int res;
    for(int j=0; j<min(itterations,pointCount); j++){
        
        char * tmp;
        
        tmp=root_withIndirection;
        res=performPointCorr_IntOut( data[j], tmp, rad).first;
        counter3+=res;
        
        tmp=root_withIndirection;
        performPointCorr_OnTree(data[j], tmp, rad);
        
        tmp=root_noIndirection;
        long long treeSize_   =  treeSize(pointCount, false);
        char * treeOutRoot  =  (char*) malloc(treeSize_);
        char * treeOutRoot_tmp  = treeOutRoot;
        performPointCorr_treeOut_rec(data[j],tmp , treeOutRoot_tmp, rad);
        free(treeOutRoot);
        
    }
    cout<<counter<<","<<counter2<<","<<counter3<<endl;
    assert((counter==counter2&& counter2==counter3) && "error");
}

double evlauteRuntime(Point * data,char  * root , float rad,int pointCount,int itterations,Varient mode){
    double trials[TRIALS];
    double treeOutBuildTime[TRIALS];
    int amplyfiy=(pointCount<=10000)? 1000: 1;
    
    char*  toDel[1001];
    
    for(int i=0; i<TRIALS ; i++) {
        double time_spent=0;
        double time_treeOutBuild=0;
        
        
        for(int j=0; j<min(10,pointCount); j++){
            int res;
            if(mode==Varient::intOut){
                auto t1 = std::chrono::high_resolution_clock::now();
                for(int h=0; h<amplyfiy; h++){
                    char * tmp=root;
                    res=performPointCorr_IntOut( data[j], tmp, rad).first;
                }
                auto t2 = std::chrono::high_resolution_clock::now();
                time_spent+=std::chrono::duration_cast<std::chrono::microseconds>(t2-t1).count();
            }
            else if(mode==Varient::updateTree){
                auto t1 = std::chrono::high_resolution_clock::now();
                for(int h=0; h<amplyfiy; h++){
                    char* tmp=root;
                    performPointCorr_OnTree(data[j], tmp, rad);
                }
                auto t2 = std::chrono::high_resolution_clock::now();
                time_spent+=std::chrono::duration_cast<std::chrono::microseconds>(t2-t1).count();
                
            }
            else if(mode==Varient::treeOut){
                
                //build output tree
                long long treeSize_   =  treeSize(pointCount, false);
                
                auto t1 = std::chrono::high_resolution_clock::now();
                for(int h=0; h<amplyfiy; h++){
                    char *tmp_in=root;
                    char * treeOutRoot  =  (char*) malloc(treeSize_);
                    toDel[h] = treeOutRoot;
                    performPointCorr_treeOut_rec(data[j],tmp_in , treeOutRoot, rad);
                }
                auto t2 = std::chrono::high_resolution_clock::now();
                time_spent+=std::chrono::duration_cast<std::chrono::microseconds>(t2-t1).count();
                for(int h=0; h<amplyfiy; h++){
                    free(toDel[h]);
                }
            }
            else
                assert(false && "wrong arg 3");
            
        }
        time_spent /=1000000;
        time_treeOutBuild/=1000000;
        
        
        printf("  run(%d): %lf--%lf\n", i, time_spent,time_treeOutBuild);
        trials[i] = time_spent;
        treeOutBuildTime[i]=time_treeOutBuild;
    }
    double avgTime;
    double avgTreeOutBuildTime=0;
    double sum=0;
    double sum_buildTime=0;
    for(int i=0; i<TRIALS; i++){
        sum+=trials[i];
        sum_buildTime+=treeOutBuildTime[i];
    }
    avgTime=sum/TRIALS;
    avgTreeOutBuildTime=sum_buildTime/TRIALS;
    return avgTime+avgTreeOutBuildTime;
}


int main(int argc, char **argv){
    
    
    //reading inputs and building point list
    Point * data;
    float rad;
    int pointCount;
    Varient mode;
    int itterations;
    readInput(argc,  argv, data, rad, pointCount,mode);
    
    if(pointCount>100000){
        itterations=10;
    }
    else{
        itterations=100;
    }
    
    cout<<"benchmarking mode: "<<(mode==Varient::intOut? "intout":(mode== Varient::treeOut ? ("treeout"): ( mode== Varient::updateTree? ("updatetree"):("error!") )))<<endl;
    
    cout<<"points data of size " <<pointCount<<" are loaded "<<endl;
    
    auto t1 = std::chrono::high_resolution_clock::now();
    char *root_withIndirection=NULL;
    char * root_noIndirection=NULL;
    
#ifdef TEST
    root_withIndirection=buildTree(pointCount ,  data, true);
    root_noIndirection=buildTree(pointCount ,  data, false);
#else
    
    if(mode==Varient::intOut || mode==Varient::updateTree)
        root_withIndirection=buildTree(pointCount ,  data, true);
    
    else if(mode==Varient::treeOut)
        root_noIndirection=buildTree(pointCount ,  data, false);
#endif
    
    auto t2 = std::chrono::high_resolution_clock::now();
    double time_spent =  std::chrono::duration_cast<std::chrono::microseconds>(t2-t1).count()/1000000;
    printf("done building two trees, took %lf seconds\n\n", time_spent);
    
    
#ifdef TEST
    doTest(data, root_noIndirection, root_withIndirection, rad, pointCount, itterations);
#else
    
    //running the traversal
    double avgTime;
    if(mode==Varient::treeOut)
        avgTime=evlauteRuntime(data,root_noIndirection , rad, pointCount, itterations, mode);
    else
        avgTime=evlauteRuntime(data,root_withIndirection , rad, pointCount, itterations, mode);
    
    
    //write results
    string benchamrk_name=(mode==Varient::intOut)?
    "handwritten-c-packed-intout":((mode==Varient::treeOut)? "handwritten-c-packed-treeout":"handwritten-c-packed-updatetree");
    
    
    unsigned long long memoryUsage;
    
    
    if(mode==Varient::intOut ||mode==Varient::updateTree){
        memoryUsage=sizeof(Node_Leaf)*pointCount+sizeof(Node_Inner_Indirection)*nodeCount_INNER +
        (nodeCount_INNER+pointCount)*(sizeof(char));
    }
    else if(mode==Varient::treeOut){
        memoryUsage=sizeof(Node_Leaf)*pointCount+sizeof(Node_Inner_NoIndirection)*nodeCount_INNER+
        (nodeCount_INNER+pointCount)*(sizeof(char));
    }
    
    printf("res:[%s,%s,%d,%d,%llu,%f]\n", "kd-tree", &benchamrk_name[0], pointCount, TRIALS, memoryUsage, avgTime );
#endif
    
    delete [] data;
    
#ifdef TEST
    
    free(root_noIndirection);
    free(root_withIndirection);
#else
    
    if(mode==Varient::intOut || mode==Varient::updateTree)
        free(root_withIndirection);
    
    else if(mode==Varient::treeOut)
        free(root_noIndirection);
#endif
    return 0;
    
}

int compare_doubles (const void *a, const void *b){
    const double *da = (const double *) a;
    const double *db = (const double *) b;
    return (*da > *db) - (*da < *db);
}
