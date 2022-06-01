## CR1_SFE_FA_RW

# Exercice 1 Addition
```c
//A faire en rajoutant les bonnes préconditions
```

# Exercice 2 Distance


```c
#include <limits.h>
/*@
  requires (INT_MIN <= (b - a) <= INT_MAX) && (INT_MIN <= (a - b) <= INT_MAX);
  ensures (a < b) ==> \result == b - a;
  ensures (a >= b) ==> \result == a - b;
*/
int distance(int a, int b){
    if(a < b) return b - a ;
    else return a - b ; 
}
```
On a choisi d'abord de mettre des préconditions pour vérifier que nos paramètres sont des les limites des entiers.
Puis on vérifie la sortie en fonction des conditions sur a, b et /result.

# Exercice 3 Alphabet


```c
#include <limits.h>
/*@
requires (0 <= c <= 127 );
ensures (( 'a' <=c <='z') || ('A' <= c <= 'Z')) && \result == 1;
*/
int alphabet_letter(char c){
    if( ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') ) return 1 ;
    else return 0 ;
}

int main(){ int r ;
    r = alphabet_letter('x') ;
    //@ assert r ;
    r = alphabet_letter('H') ;
    //@ assert r ;
    r = alphabet_letter(' ') ;
    //@ assert !r ;
}
```

