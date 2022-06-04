## CR1_SFE_Frédéric ALPHONSE_Roman WOLFENSPERGER
![IMG_0978](https://user-images.githubusercontent.com/101244166/171950332-e927d53f-aeeb-41bd-99cd-c974be30a3c0.PNG)


### Analyser et commeneter les résultats d'analyses

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

# Exercice 4 Jours du Mois

Pour moi le code est très proche de la solution mais je ne comprends pas la réponse de frama c
```c
/*@
requires ( 1<=month <= 12 );

ensures (( month == 4 || month == 6 || month == 9 || month == 11 ==> \result == 30));

ensures ((month == 1 || month == 3 || month == 5 || month == 7 || month == 8 || month == 10 ||	month ==12 ==> \result == 31));

ensures (month == 2 ==>\result == 28);

*/
int day_of(int month){
    int days[] = { 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 } ;
    return days[month-1] ;
}

```
