# Testing

## Testing strutturale (white-box)

Il **testing strutturale** tiene conto della struttura interna del programma con l'obiettivo di sollecitare tutte le parti del programma e, quindi, molto costoso da implementare.

### Criterio di copertura delle istruzioni (statement coverage)

Si vuole fare in modo che ogni istruzione del programma venga eseguita almeno una volta.
Consideriamo la seguente funzione:

```java
int sqrt(int n) {
  int i = 1, z = 1;
  if(n < 0) 
    return -1;
  while(z <= n) {
    i = i + 1;
    z = i * i;
  }
  return i - 1;
}
```

Dobbiamo selezionare dei casi di testi in modo che ogni istruzione venga eseguita almeno una volta.
possiamo scegliere i seguenti casi di test:

- `n = -1` per eseguire il corpo dell'`if`
- `n = 1` per eseguire il corpo del `while`

_Osservazione_: se una funzione ha n `return` allora avremo per forza **almeno n casi di test**.

### Criterio di copertura delle decisioni (edge coverage)

Si vuole coprire tutte le possibili _diramazioni_ del programma. per fare ciò è utile costruire il **control flow graph** (o **CFG**) del programma in cui si evidenziono proprio tutte le diramazioni.
Nella figura seguente è riportato il CFG della funzione `sqrt` (esempio precedente):

![](./immagini/cfg.svg)

Ogni arco rappresenta una possibile diramazione. Si noti che ogni `if` e `while` sono rappresentati da due archi, uno per il caso `true` e uno per il caso `false` (anche se ad esempio il ramo `else` non è esplicitamente presente nel codice).

Il criterio **edge coverage** vuole che ogni arco del CFG venga eseguito almeno una volta. Per fare ciò possiamo scegliere i seguenti casi di test:

- `n = -1` per eseguire solo l'arco `n < 0` (e finire il programma)
- `n = 1` per eseguire il ramo else del primo `if` e per entrare nel `while` (e quindi eseguire tutti e due gli archi del `while`)

### Criterio di copertura delle decisioni e delle condizioni (edge and condition coverage)

L’insieme dei casi di test deve essere definito in modo che ogni ramo del CFG venga attraversato almeno una volta e con **tutti i possibili valori** nelle sottoespressioni che compaiono nelle condizioni composte.

Per esempio, consideriamo la seguente funzione:

```java
void p(int x, int y) {
  if(x == 0 || y > 0)
    y = y/x;
  else
    y = (-y)/x;
}
```

Si può entrare nel ramo `if` nei seguenti modi: `x = 0, y <= 0` e `x != 0, y > 0`

e nel ramo `else`: `x != 0` e `y <= 0`.

Sono quindi sufficienti 3 casi di test: `x = 0, y = -1`, `x = 1, y = 1` e `x = 1, y = -1`.

---

### Criterio di copertura dei cammini (path coverage)

L’insieme dei casi di test deve garantire che ogni possibile cammino (o percorso) che porti dal nodo iniziale al nodo finale del CFG sia percorso almeno una volta.

_Attenzione_: il numero di volte in qui si esegue un ciclo (un autoanello nel CFG) è rilevante. Perciò, se un ciclo può essere eseguito "infinite" volte, allora il criterio di copertura dei cammini non è applicabile. Ad esempio considerando la funzione di prima `int sqrt(int n)`, `n` può essere grande "quanto vogliamo" (in realtà non è così, dato che è un intero a 32 bit, ma supponiamo che sia così), pertanto il ciclo `while` può essere eseguito "infinite volte". Il criterio non è quindi applicabile.

Consideriamo, per esempio, la seguente funzione:

```java
int f(int x, int y) {
  int z = 0;
  if(x > 0) {
    if(y > 0) {
      z = x + y;
    } else {
      z = x - y;
    }
  } else {
    if(y > 0) {
      z = x * y;
    } else {
      z = x / y;
    }
  }
  return z;
}
```

I possibili cammini sono 4:

- `x > 0, y > 0` prendendo il primo ramo dell'`if` esterno e il primo ramo dell'`if` interno al ramo `if`
- `x > 0, y <= 0` prendendo il primo ramo dell'`if` esterno e il secondo ramo `else` interno al ramo `if`
- `x <= 0, y > 0` prendendo il secondo ramo `else` esterno e il primo ramo dell'`if` interno al ramo `else`
- `x <= 0, y <= 0` prendendo il secondo ramo `else` esterno e il secondo ramo `else` interno al ramo `else`

## Esercizio sul testing (TdE del 2020-01-16, esercizio 4)

Si consideri il seguente frammento di codice:

```java
int f(int a, int b) {
  if(a > b) {
    System.out.println("A");
  } else {
    System.out.println("B");
  }
  for(int i = 0; i < 1000; i++) {
    if(a > 0) break;
    else a = 1;
  }
}
```

### Domanda a)

Definire un insieme minimo di casi di test per coprire tutte le istruzioni (statement coverage)

#### Soluzione

Sono sufficienti 2 casi di test:

- `a = 1, b = 0` per eseguire il ramo `if` del primo `if` e il `break` interno al `for`
- `a = 0, b = 1` per eseguire il ramo `else` del primo `if` e sia `a=1` che il `break` nel `for`

### Domanda b)

Definire un insieme minimo di casi di test per coprire tutte le decisioni (edge coverage)

#### Soluzione

Si noti che il ciclo `for` può essere eseguito al massimo 2 volte e poi il `break` lo interrompe. Non è quindi possibile coprire la decisione `i<1000`. Tutte le altre decisioni sono coperte dai 2 casi precedenti.

### Domanda c)

Definire un insieme minimo di casi di test per coprire tutti i cammini (path coverage)

#### Soluzione

Quindi, il corpo del `for` può essere eseguito 1 volta (se si entra direttamente nell'`if` e si esegue il break) o 2 volte (se si entra nell'`else`, per poi eseguire `break` la seconda iterazione). Per cui abbiamo 4 possibili cammini (quindi 4 casi di test):

- `a = 1, b = 0` per eseguire il primo `if` e il corpo del `for` una volta
- `a = 1, b = 2` per eseguire il primo `else` e il corpo del `for` una volta
- `a = -1, b = 0` per eseguire il primo `else` e il corpo del `for` due volte
- `a = -1, b = -2` per eseguire il primo `if` e il corpo del `for` due volte
