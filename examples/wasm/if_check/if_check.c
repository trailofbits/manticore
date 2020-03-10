#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

int main() {
    uint8_t i = getchar();

    int branch_counter = 1;
    if (!(128 & i)){       branch_counter++;
     if (64 & i){          branch_counter++;
      if (!(32 & i)){      branch_counter++;
       if (16 & i){        branch_counter++;
        if (8 & i){        branch_counter++;
         if (!(4 & i)){    branch_counter++;
          if (!(2 & i)){   branch_counter++;
           if (!(1 & i)){  branch_counter++;
            printf("You got it!\n");
            return 0;
           }
          }
         }
        }
       }
      }
     }
    }

    printf("You lose :/\n");
    return -1 * branch_counter;

}