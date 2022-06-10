## CR1_SFE_Frédéric ALPHONSE_Roman WOLFENSPERGER
![IMG_0978](https://user-images.githubusercontent.com/101244166/171950332-e927d53f-aeeb-41bd-99cd-c974be30a3c0.PNG)
## Notes
Highlight un mot `exemple` et gras `limits.h`
### Analyser et commenter les résultats d'analyses

# Exercice 1 Addition
```c
#include <limits.h>

/*@
  requires INT_MIN <= x+y <= INT_MAX
  ensures INT_MIN <= \result <= INT_MAX;
*/
int add(int x, int y){
    return x+y ;
}
```

**Voici le code du résultat d'analyse :**
```c
/*@ requires -2147483647 - 1 ≤ x + y ≤ 2147483647;
    ensures -2147483647 - 1 ≤ \result ≤ 2147483647;
 */
int add(int x, int y)
{
  int __retres;
  /*@ assert rte: signed_overflow: -2147483648 ≤ x + y; */
  /*@ assert rte: signed_overflow: x + y ≤ 2147483647; */
  __retres = x + y;
  return __retres;
}
```


#### Commenter
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

**Voici le code du résultat d'analyse :**
```c
/*@ requires
      -2147483647 - 1 ≤ b - a ≤ 2147483647 ∧
      -2147483647 - 1 ≤ a - b ≤ 2147483647;
    ensures \old(a) < \old(b) ⇒ \result ≡ \old(b) - \old(a);
    ensures \old(a) ≥ \old(b) ⇒ \result ≡ \old(a) - \old(b);
 */
int distance(int a, int b)
{
  int __retres;
  if (a < b) {
    {
      /*@ assert rte: signed_overflow: -2147483648 ≤ b - a; */
      /*@ assert rte: signed_overflow: b - a ≤ 2147483647; */
      __retres = b - a;
      goto return_label;
    }
  }
  else {
    {
      /*@ assert rte: signed_overflow: -2147483648 ≤ a - b; */
      /*@ assert rte: signed_overflow: a - b ≤ 2147483647; */
      __retres = a - b;
      goto return_label;
    }
  }
  return_label: return __retres;
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



**Voici le code du résultat d'analyse :**
```c
int main(void)
{
  int __retres;
  int r;
  r = alphabet_letter((char)'x');
  /*@ assert r ≢ 0; */ ;
  r = alphabet_letter((char)'H');
  /*@ assert r ≢ 0; */ ;
  r = alphabet_letter((char)' ');
  /*@ assert r ≡ 0; */ ;
  __retres = 0;
  return __retres;
}
```


# Exercice 4 Jours du Mois
## Pour moi le code est très proche de la solution mais je ne comprends pas la réponse de frama c. Même résultat entre mon Code et les autres
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


**Voici le code du résultat d'analyse :**
```c
/*@ requires 1 ≤ month ≤ 12;
    ensures
      \old(month) ≡ 4 ∨ \old(month) ≡ 6 ∨ \old(month) ≡ 9 ∨
      \old(month) ≡ 11 ⇒ \result ≡ 30;
    ensures
      \old(month) ≡ 1 ∨ \old(month) ≡ 3 ∨ \old(month) ≡ 5 ∨
      \old(month) ≡ 7 ∨ \old(month) ≡ 8 ∨ \old(month) ≡ 10 ∨
      \old(month) ≡ 12 ⇒ \result ≡ 31;
    ensures \old(month) ≡ 2 ⇒ \result ≡ 28;
 */
int day_of(int month)
{
  int __retres;
  int days[12] = {31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31};
  /*@ assert rte: signed_overflow: -2147483648 ≤ month - 1; */
  /*@ assert rte: index_bound: 0 ≤ (int)(month - 1); */
  /*@ assert rte: index_bound: (int)(month - 1) < 12; */
  __retres = days[month - 1];
  return __retres;
}
```

# Exercice 5 Triangle

#### commenter
```c
#include <limits.h>
/*@
  requires (0<= first <=180) && (0<= second <=180);
  ensures (\result + first + second) == 180;
*/

int last_angle(int first, int second){
    return 180 - first - second ;
}

```

**Voici le code du résultat d'analyse :**
```c
/*@ requires 0 ≤ first ≤ 180 ∧ 0 ≤ second ≤ 180;
    ensures (\result + \old(first)) + \old(second) ≡ 180;
 */
int last_angle(int first, int second)
{
  int __retres;
  /*@ assert rte: signed_overflow: 180 - first ≤ 2147483647; */
  /*@ assert
      rte: signed_overflow: -2147483648 ≤ (int)(180 - first) - second;
  */
  /*@ assert rte: signed_overflow: (int)(180 - first) - second ≤ 2147483647;
  */
  __retres = (180 - first) - second;
  return __retres;
}

```


## Conclusion
