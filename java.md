# Java

## Le classi

Vediamo un esempio di classe che rappresenta una data.

```java
public class Data {
  private int giorno;
  private int mese;
  private int anno;

  // Restituisce il giorno
  public int ottieniGiorno() {
    return giorno;
  }

  // Restituisce il mese
  public int ottieniMese() {
    return mese;
  }

  // Restituisce l'anno
  public int ottieniAnno() {
    return anno;
  }
}
```

Una classe può essere interpretata come un tipo definito dall'utente che specifica anche le operazioni che vi si possono effettuare. Questo tipo può essere usato per dichiarare altre variabili, ad esempio: `Date d;`.

Gli **attributi** della classe `Data` sono: `giorno`, `mese` e `anno`. I **metodi** invece sono: `ottieniGiorno`, `ottieniMese`, `ottieniAnno`.

All'interno dell'implementazione di ciascun metodo (non statico) possiamo utilizzare la keyword **`this`** per fare riferimento all'oggetto su cui il metodo è stato invocato.

In Java è possibile invocare i metodi tramite la **dot notation**, ad esempio:
```java
Data d = new Data();
int x;

x = d.ottieniGiorno();
```

Invocare un metodo su un oggetto può cambiarne lo stato.
Supponiamo che la classe `Data` si trovi in questo stato iniziale:
```java
System.out.println(d.ottieniGiorno() + "/" + 
d.ottieniMese() + "/" d.ottieniAnno());
```
```bash
30/11/2011
```
e che siano stati definiti due nuovi metodi:
```java
public Class Data {
  ...
  private int numeroGiorni() {
    switch (mese) {
    case 1:
      return 31;
    case 2:
      return 28;
    ...
    case 12:
      return 31;
    default:
      return -1;
    }
  }
  ...
  private void giornoDopo {
    giorno++;
    if (giorno > numeroGiorni()) {
      giorno = 1;
      mese++;
    }
    if (mese > 12) {
      mese = 1;
      anno++;
    }
  }
  ...
}
```
Allora se invochiamo `giornoDopo`:
```java
d.giornoDopo();

System.out.println(d.ottieniGiorno() + "/" + 
d.ottieniMese() + "/" d.ottieniAnno());
```
```bash
1/12/2011
```

---

## Collections

Le **Collections** permettono di gestire insiemi di oggetti.

### List

La classe `java.util.List` è un'interfaccia che rappresenta una lista ordinata di elementi. Ecco i metodi disponibili per questa interfaccia:

- **`void add(int index, E element)`**: aggiunge un elemento alla posizione specificata nella lista. Restituisce nulla.
- **`boolean add(E e)`**: aggiunge un elemento alla fine della lista. Restituisce true se l'elemento viene aggiunto con successo, false altrimenti.
- **`boolean addAll(Collection<? extends E> c)`**: aggiunge tutti gli elementi di una collezione alla fine della lista. Restituisce true se almeno un elemento viene aggiunto con successo, false altrimenti.
- **`boolean addAll(int index, Collection<? extends E> c)`**: aggiunge tutti gli elementi di una collezione alla posizione specificata nella lista. Restituisce true se almeno un elemento viene aggiunto con successo, false altrimenti.
- **`void clear()`**: rimuove tutti gli elementi dalla lista. Restituisce nulla.
- **`boolean contains(Object o)`**: verifica se l'oggetto specificato è presente nella lista. Restituisce true se l'oggetto è presente nella lista, false altrimenti.
- **`boolean containsAll(Collection<?> c)`**: verifica se tutti gli elementi di una collezione sono presenti nella lista. Restituisce true se tutti gli elementi sono presenti nella lista, false altrimenti.
- **`boolean equals(Object o)`**: verifica se la lista è uguale a un altro oggetto. Restituisce true se l'oggetto è uguale alla lista, false altrimenti. _Attenzione_: se l'oggetto passato è una lista, allora controlla se le liste hanno stesso numero di elementi e se gli elementi sono uguali (le liste sono uguali).
- **`E get(int index)`**: restituisce l'elemento presente nella posizione specificata nella lista.
- **`int indexOf(Object o)`**: restituisce l'indice della prima occorrenza dell'oggetto specificato nella lista. Restituisce -1 se l'oggetto non è presente nella lista.
- **`boolean isEmpty()`**: verifica se la lista è vuota. Restituisce true se la lista è vuota, false altrimenti.
- **`Iterator<E> iterator()`**: restituisce un iteratore per la lista.
- **`int lastIndexOf(Object o)`**: restituisce l'indice dell'ultima occorrenza dell'oggetto specificato nella lista. Restituisce -1 se l'oggetto non è presente nella lista.
- **`ListIterator<E> listIterator()`**: restituisce un iteratore bidirezionale per la lista.
- **`ListIterator<E> listIterator(int index)`**: restituisce un iteratore bidirezionale per la lista a partire dalla posizione specificata.
- **`E remove(int index)`**: rimuove l'elemento presente nella posizione specificata nella lista. Restituisce l'elemento rimosso.
- **`boolean remove(Object o)`**: rimuove la prima occorrenza dell'oggetto specificato nella lista. Restituisce true se l'oggetto viene rimosso con successo, false altrimenti.
- **`boolean removeAll(Collection<?> c)`**: rimuove dalla lista tutti gli elementi presenti in una collezione. Restituisce true se almeno un elemento viene rimosso con successo, false altrimenti.
- **`boolean retainAll(Collection<?> c)`**: rimuove dalla lista tutti gli elementi che non sono presenti in una collezione. Restituisce true se almeno un elemento viene rimosso con successo, false altrimenti.
- **`E set(int index, E element)`**: sostituisce l'elemento presente nella posizione specificata nella lista con un nuovo elemento. Restituisce l'elemento sostituito.
- **`int size()`**: restituisce il numero di elementi presenti nella lista.
- **`List<E> subList(int fromIndex, int toIndex)`**: restituisce una sottolista della lista compresa tra gli indici specificati.
- **`Object[] toArray()`**: restituisce un array di oggetti contenente tutti gli elementi della lista.
- **`<T> T[] toArray(T[] a)`**: restituisce un array di tipo specificato contenente tutti gli elementi della lista.

