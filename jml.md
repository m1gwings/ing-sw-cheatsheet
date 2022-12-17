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

### Condizioni

Le condizioni in JML (precondizioni e postcondizioni) sono espressioni booleane di Java (con alcuni operatori e quantificatori aggiuntivi) che non alterano lo stato degli oggetti che descrivono: non si possono usare assegnamenti (`=`), incrementare le variabili intere (`++`), etc. Gli unici metodi che si possono invocare sono quelli che non modificano lo stato degli oggetti a cui appartengono o dei parametri che gli vengono passati (si dicono **metodi puri**).

#### Operatori aggiuntivi

Siano `a` e `b` due condizioni JML, allora le seguenti sono valide condizioni JML:

- `a ==> b`: `a` implica `b`
- `a <== b`: `b` implica `a`
- `a <==> b`: `a` se e solo se `b`
- `a <=!=> b`: `!(a <==> b)`
- `\old(a)`: l'operatore `\old` è da utilizzare all'interno di una postcondizione. Restituisce il valore della condizione `a`, valutata prima che il metodo venga eseguito.

#### Quantificatori

Siano `a` e `b` due condizioni JML e `T` un generico tipo di Java, allora le seguenti sono valide condizioni JML:

- `(\forall T t; a; b)`: per ogni oggetto del tipo `T` (nel caso `T` non sia un tipo primitivo, i valori )