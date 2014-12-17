int f(int i){
  if(i > 0){
    return f(i--);
  }
  return 5;
}

int main(){
  f(20);
  return 5;
}
