int a[] = {1,3,2,4,5};

void swap(int i, int j){
    if(a[i] > a[j]){
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

int main(){
    swap(1,2);
    return 0;
}
