int collatz(int x){
  if (x <= 1){
    return 0;
  }
  if (x % 2 == 0){
   return collatz(x / 2) + 1;
  }
  else{
   return collatz(3 * x + 1) + 1;
  }
}

int main() {
  return collatz(getchar(">"));
}