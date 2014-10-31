int a[] = {1,3,2,4,5};

int main(){
    int i = 1;
    int j = 2;
    if(a[i] > a[j]){
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
    return 0;
}
