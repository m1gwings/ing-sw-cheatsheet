# JML

**JML** (Java Modeling Language) è un linguaggio di specifica formale.

## Sintassi

Lo schema generale di una specifica in JML è il seguente:
```java
// OVERVIEW: descrizione della specifica
//@ assignable <parametri che possono essere 
//@    modificati dal metodo>;
//@ requires <precondizione>
//@ ...;
//@ ensures <postcondizione>
//@ ...;
//@ signals (<tipo eccezione 1> e)
//@ <postcondizione nel caso di eccezione 1>
//@ ...;
//@ signals (<tipo eccezione 2> e)
//@ <postcondizione nel caso di eccezione 2>
//@ ...;
```
Ogni riga della specifica (dopo l'`OVERVIEW`) inizia con `//@ `.
Alla fine di ciascun "blocco" (`assignable`, `requires`, ...) è necessario aggiungere `;`.
Omettere il blocco `requires` equivale a scrivere `//@ requires true;`.
Omettere il blocco `ensures` equivale a scrivere `//@ ensures true;`.
Nella condizione del blocco `signals` possiamo fare riferimento all'oggetto eccezione `e` (il nome è arbitrario).

### Condizioni

Le condizioni in JML (precondizioni e postcondizioni) sono espressioni booleane di Java (con alcuni operatori e quantificatori aggiuntivi) che non alterano lo stato degli oggetti che descrivono: non si possono usare assegnamenti (`=`), incrementare le variabili intere (`++`), etc. Gli unici metodi che si possono invocare sono quelli che non modificano lo stato degli oggetti a cui appartengono o dei parametri che gli vengono passati (si dicono **metodi puri**).

#### Operatori booleani aggiuntivi

Siano `a` e `b` due condizioni JML, allora le seguenti sono valide condizioni JML:

- `a ==> b`: `a` implica `b`
- `a <== b`: `b` implica `a`
- `a <==> b`: `a` se e solo se `b`
- `a <=!=> b`: `!(a <==> b)`

#### `\old`

L'operatore `\old(<espressione>)` prende in input una espressione che può essere una condizione JML oppure una espressione Java che non ha "effetti collaterali" (non si può utilizzare `++`, `=`, metodi **non** puri, etc.) e restituisce il risultato che si ottiene valutando tale espressione nel momento della chiamata del metodo che stiamo specificando.
Notare che, valutando una espressione Java (tra quelle ammissibili), `\old` in generale non restituisce valori booleani.
Non ha senso utilizzare `\old` nel blocco `requires` dato che lì stiamo specificando ciò che deve essere vero **prima** che il metodo venga eseguito.

#### Quantificatori

Sia `T` un generico tipo di Java ed `a(t)`, `b(t)` due condizioni JML definite su un oggetto `t` di tipo `T` (ad esempio se `T = int`, `a(t) = t > 1729`), allora le seguenti sono valide condizioni JML:

- `(\forall T t; a(t); b(t))`: per ogni oggetto del tipo `T` se `a(t)` allora `b(t)`
- `(\exists T t; a(t); b(t))`: esiste un oggetto del tipo `T` tale che `a(t)` e `b(t)`
- `(\num_of T t; a(t); b(t))`: restituisce il numero di oggetti `t` tale che `a(t)` e `b(t)`

Nel caso `T` non sia un tipo primitivo assumiamo `t != null`.

#### Operatori di aggragazione

Sia `T` un generico tipo di Java ed `N` uno dei tipi numerici primitivi di Java (`int`, `float`, ...).
Sia `a(t)` una condizione JML definita sull'oggetto `t` di tipo `T`.
Sia `b : T -> N` una funzione (in senso matematico) implementata attraverso Java. Ad esempio:
`T = String`, `N = int`, `a(t) = !t.isEmpty() && t.charAt(0) == 'e'`, `b(t) = t.length()`.
Allora possiamo applicare i seguenti operatori di aggragazione:

- `(\sum T t; a(t); b(t))`: restituisce la somma `b(t_1) + b(t_2) + ...` per tutti i `t_i` tali che `a(t_i)`
- `(\product T t; a(t); b(t))`: restituisce il prodotto `b(t_1)*b(t_2)*...` per tutti i `t_i` tali che `a(t_i)`
- `(\max T t; a(t); b(t))`: restituisce il massimo tra `b(t_1), b(t_2), ...` per tutti i `t_i` tali che `a(t_i)`
- `(\min T t; a(t); b(t))`: restituisce il minimo tra `b(t_1), b(t_2), ...` per tutti i `t_i` tali che `a(t_i)`

### `\result`

Se stiamo scrivendo la specifica di un metodo NON `void`, possiamo fare riferimento al valore restituito con la keyword `\result`.
Ha senso utilizzare `\result` solo nell'`ensures` (in `requires` il metodo non è ancora stato eseguito, `signals` specifica la postcondizione qualora venga restituita un'eccezione).

### `assignable`

Il blocco `assignable` nella specifica permette di esplicitare i parametri (di tipo riferimento) che vengono modificati dal metodo.
Omettere `assignable` significa che tutti i parametri possono essere modificati.

Se un metodo non modifica nessuno dei parametri possiamo usare la keyword `\nothing`:
`//@ assignable \nothing;`.

Consideriamo il seguente metodo:
```java
public static void metodo(S s, T t, U u) {
    ...
}
```
Per specificare che `s` e `t` vengono modificati, ma non `u`, possiamo aggiungere nella specifica:
`//@ assignable s, t;`

---

Supponiamo di voler specificare che un array `a[]` venga modificato da un metodo di cui stiamo scrivendo la specifica:

- `//@ assignable a[*];`: ogni elemento di `a` può essere modificato
- `//@ assignable a[5];`: solo l'elemento `a[5]` può essere modificato
- `//@ assignable a[1..8];`: gli elementi `a[1]`, `a[2]`, ..., `a[8]` possono essere modificati

### Commenti

A volte è utile inserire all'interno delle condizioni JML delle specifiche informali.
Per farlo si utilizzano i commenti, esprimibili attraverso la seguente sintassi: `(* <commento> *)`.
Ciascun commento al momento della valutazione della condizione è da intendersi con valore `true`.

## Semantica

### Precondizione

La **precondizione** è la condizione sulla base della quale è definita la specifica: se la precondizione non dovesse essere rispettata allora non è detto che il metodo si comporti secondo la specifica (in generale non lo farà, qualsiasi comportamento è ammesso).
In JML è possibile esprimere una precondizione del metodo che stiamo specificando attraverso il blocco `requires`.
Nel caso in cui la precondizione sia `true` il metodo "non ha una precondizione": la sua specifica è valida a prescindere dei parametri passati.
Un metodo con precondizione `true` si dice **totale**, altrimenti si dice **parziale**.

### Postcondizione

La **postcondizione** esplicita una serie di "effetti" garantiti al termine dell'esecuzione del metodo che stiamo specificando, assumendo che la precondizione fosse verificata.
In JML è possibile definire separatamente la postcondizione che vale nel caso in cui il metodo esegua regolarmente dalle postcondizioni che valgono nel caso in cui durante l'esecuzione del metodo si verifichino delle eccezioni.
La prima si esplicita attraverso il blocco `ensures`.
La seconda attraverso `signals (<tipo eccezione> e)`.
Nel caso in cui la postcondizione sia `true` il metodo non garantisce nessun "effetto" al termine della sua esecuzione, quindi può "fare ciò che vuole": non c'è motivo di omettere la postcondizione.

<!-- TODO:
 - I metodi puri non hanno bisogno che nella specifica si espliciti che l'oggetto non cambia
 - assertions (di secondaria importanza)  -->