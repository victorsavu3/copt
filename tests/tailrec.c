int i = 10;
int a = 1;

void f(){
  if(i > 0){
    a += i*i;
    i--;
    f();
  }
}

int main(){
  f();
  return a;
}
