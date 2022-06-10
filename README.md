## CR1_SFE_Frédéric ALPHONSE_Roman WOLFENSPERGER

**Rédacteurs :** Frédéric ALPHONSE et Roman WOLFENSPERGER

**Encadrants :** Sébastian FAUCOU et Pierre-Emmanuel HLADIK
![IMG_0978](https://user-images.githubusercontent.com/101244166/171950332-e927d53f-aeeb-41bd-99cd-c974be30a3c0.PNG)
## Notes
Highlight un mot `exemple` et gras **limits.h** et italique *exemple*

## Introduction :

Au fil des années, on a vu qu'il y a de plus en plus d'incidents dans les systèmes critiques dues à des erreurs facilement évitables avec des outils et des logiciels adéquats. Il n'est donc pas sans raison qu'on a vu l'apparition d'outils comme `frama-c` ou `metrics` pour éviter au maximum les erreurs via le respect de règles et les normes. Parmi, les célèbres accidents on peut citer celui d'Ariane 5 dû à une mauvaise conversion d'un entier 16 bits à 8 bits entraînant une défaillance non prise en compte. Ce TP nous permet ainsi de mieux connaître ses outils et savoir programmer du code des systèmes critiques en adoptant la bonne conduite.


# Exercice 1 Addition

**Code Implémenté :**
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

*Commentaire :*

La précondition permet de vérifier que la sommes des deux entiers soit comprises dans les limites du type entier. En effet, lorsque l'on fait l'addition de deux entiers 32 bits. Il est possible que la somme dépasse les 32 bits puisqu'elle est comprise dans 64 bits. La précondition nous permet d'éviter le débordement. Puis, nous rajoutant la post condition pour réaliser le test d'inclusion dans la limite entière du résultat.

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
**Analyse :**

On peut voir que toutes les pastilles sont vertes donc que les tests sont bien implémentés, de plus on peut voir que les asserts nous avertit du fameaux débordement des entiers.

# Explications sur les asserts

L'assert est un outil essentiel dans les systèmes critique. Il permet de d'arrêter si le programme est **false** ou de le continuer si le résultat est **true**.





# Exercice 2 Distance

**Code Implémenté :**
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
**Analyse et commentaire :**

On utilise deux précondtions pour s'assurer que la soustraction de a-b et b-a soit compris dans les limites du type entier de 32 bits, pour aussi éviter les débordements. Puis, pour tester notre fontion on vérifie que notre que les résultat (/result) dépend des bonnes conditions sur a et b. De la même manière que sur l'exercice  frama-c nous prévient du débordement via les asserts.


# Exercice 3 Alphabet

**Code Implémenté :**
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

**Analyse et commentaire :**
# Table de vérité implication:
On a rajouter la  pré-condtion pour s'assurer que la variable `c` est comprise dans l'ensemble des codes ASCII des lettres au nombres.

Puis, nous testons notre  condition *if* avec nos post-conditions qui vérifie que nous le résultat est un *1* si on a une lettre de l'alphabet. Le résultat d'analyse nous affirme que notre test est fonctionnelle via les pastilles vertes et les asserts. En effet, le programme s'arrête quand le résultat est faux  à cause de l'espace via l'assert.


# Exercice 4 : Jours du Mois (Voir ma VM)

**Code Implémenté :**
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

**Analyse et commentaire :**

On utilise d'abord la pré-condition pour s'assurer que notre variable d'entrée est comprise dans la plage entre 1 et 12 soit la plage des mois.
Puis, on utilise des post-conditions pour tester que la fonction day_of, renvoie le bon résultat en fonction du nombre de fois. On a choisi au début de regrouper le code via des signes  `ou (||)`, mais nous avons remarquer que toutes nos pastilles n'étaient pas vertes.

On a donc ensuite décomposer les pré-conditions mois par mois et tout s'est bien déroulé. L'explication est que frama-c a des difficultés avec des multiples conditions.


# Exercice 5 Triangle

#### commenter

**Code Implémenté :**
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
**Analyse et commentaire :**

La fonction reçoit deux angles d'un triangle et renvoie le dernier.
On va donc tout d'abord indiquer que chacun des angles est compris entre 0  et 180° via notre programme. Puis, via la post-condition on vérifie que la fonction `last_angle` renvoie bien un angle entre 0 et 180° pour respecter la somme d'un triangle.

## Conclusion
