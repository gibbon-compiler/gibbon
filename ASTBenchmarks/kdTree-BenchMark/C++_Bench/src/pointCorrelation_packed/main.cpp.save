#include "tree_packed.h"
#include <assert.h>
#define  TRIALS 10

int counter=0;
int counter2=0;
int counter3=0;
int nodeCount=0;
int nodeCount_INNER=0;
int compare_doubles (const void *a, const void *b);

int main(int argc, char **argv){
    
    
    //reading inputs and building point list
    Point * data;
    float rad;
    int npoints;
    Varient mode;
    readInput(argc,  argv, data, rad, npoints,mode);
    cout<<"benchmarking mode: "<<(mode==Varient::intOut? "intout":(mode== Varient::treeOut ? ("treeout"): ( mode== Varient::updateTree? ("updatetree"):("error!") )))<<endl;

    cout<<"points data of size " <<npoints<<" are loaded "<<endl;
    
    clock_t begin = clock();
    char *root_withIndirection=NULL;
    char * root_noIndirection=NULL;
    
#ifdef TEST
    
    root_withIndirection=buildTree(npoints ,  data, true);
    root_noIndirection=buildTree(npoints ,  data, false);
#else

    if(mode==Varient::intOut || mode==Varient::updateTree)
        root_withIndirection=buildTree(npoints ,  data, true);
    
    else if(mode==Varient::treeOut)
        root_noIndirection=buildTree(npoints ,  data, false);
#endif

    clock_t end = clock();
    double time_spent = (double)(end - begin) / CLOCKS_PER_SEC;
    printf("done building two trees, took %lf seconds\n\n", time_spent);
    
    
#ifdef TEST
    int res;
    for(int j=0; j<min(10,npoints); j++){
        
        char * tmp;
        
        tmp=root_withIndirection;
        res=performPointCorr_IntOut( data[j], tmp, rad).first;
        counter3+=res;
        
        tmp=root_withIndirection;
        performPointCorr_OnTree(data[j], tmp, rad);
        
        tmp=root_noIndirection;
        long long treeSize_   =  treeSize(npoints, false);
        char * treeOutRoot  =  (char*) malloc(treeSize_);
        char * treeOutRoot_tmp  = treeOutRoot;
        performPointCorr_treeOut_rec(data[j],tmp , treeOutRoot_tmp, rad);        
        free(treeOutRoot);
        
    }
    cout<<counter<<","<<counter2<<","<<counter3<<endl;
    assert((counter==counter2&& counter2==counter3) && "error");
#else
    
    //running the traversal
    double trials[TRIALS];
    double treeOutBuildTime[TRIALS];

    for(int i=0; i<TRIALS; i++) {
        
        time_spent=0;
        double time_treeOutBuild=0;
        
        for(int j=0; j<min(10,npoints); j++){
            int res;
            if(mode==Varient::intOut){
               char * tmp=root_withIndirection;
                begin = clock();
                res=performPointCorr_IntOut( data[j], tmp, rad).first;
                end = clock();
                time_spent+=(double)(end - begin);

            }
            else if(mode==Varient::updateTree){
               char* tmp=root_withIndirection;
                begin = clock();
                performPointCorr_OnTree(data[j], tmp, rad);
                end = clock();
                time_spent+=(double)(end - begin);

            }
            else if(mode==Varient::treeOut){
                char *tmp_in=root_noIndirection;
                
                //build output tree
                begin = clock();
                long long treeSize_   =  treeSize(npoints, false);
                char * treeOutRoot  =  (char*) malloc(treeSize_);
                char * treeOutRoot_tmp  = treeOutRoot;
                end = clock();
                time_treeOutBuild+=(double)(end - begin);
                
                begin = clock();
                performPointCorr_treeOut_rec(data[j],tmp_in , treeOutRoot_tmp, rad);
                end = clock();
                time_spent+=(double)(end - begin);

                free(treeOutRoot);

            }
            else
                assert(false && "wrong arg 3");
            
        }
        
        
        time_spent = (double)time_spent / CLOCKS_PER_SEC;
        time_treeOutBuild=(double) time_treeOutBuild/CLOCKS_PER_SEC;
        
        printf("  run(%d): %lf--%lf\n", i, time_spent,time_spent+time_treeOutBuild);
        trials[i] = time_spent;
        treeOutBuildTime[i]=time_treeOutBuild;
        
    }
    
    
    qsort(trials, TRIALS, sizeof(double), compare_doubles);
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
    
    //write results
    string benchamrk_name=(mode==Varient::intOut)?
    "handwritten-c-packed-intout":((mode==Varient::treeOut)? "handwritten-c-packed-treeout":"handwritten-c-packed-updatetree");
    
    
    unsigned long long memoryUsage;
    
    
    if(mode==Varient::intOut ||mode==Varient::updateTree){
        memoryUsage=sizeof(Node_Leaf)*npoints+sizeof(Node_Inner_Indirection)*nodeCount_INNER +
        (nodeCount_INNER+npoints)*(sizeof(char));
    }
    else if(mode==Varient::treeOut){
        memoryUsage=sizeof(Node_Leaf)*npoints+sizeof(Node_Inner_NoIndirection)*nodeCount_INNER+
        (nodeCount_INNER+npoints)*(sizeof(char));
    }
    
    printf("res:[%s,%s,%d,%d,%llu,%f,%f]\n", "kd-tree", &benchamrk_name[0], npoints, TRIALS, memoryUsage, avgTime, avgTreeOutBuildTime + avgTime  );
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
