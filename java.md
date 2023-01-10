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

## Ereditarietà

L'**ereditarietà** è il meccanismo tramite il quale una classe può _estendere_ un'altra classe, ereditando tutte le sue variabili e metodi (a meno che questi non siano stati dichiarati come `private`). Ciò significa che una classe figlia può usare tutto ciò che è stato definito nella classe padre, e può anche aggiungere nuove funzionalità.
Per farlo si utilizza la keyword `extends`.

È inoltre possibile sovrascrivere i metodi della classe padre, cioè fornire una nuova implementazione per un metodo che è già stato definito nella superclasse. Per farlo, si può utilizzare l'annotazione `@Override` sopra al metodo che si vuole sovrascrivere.

---

Ad esempio consideriamo le seguenti classi:

```java
public class Animal {
  private String name;
  private int age;
  
  public Animal(String name, int age) {
    this.name = name;
    this.age = age;
  }
  
  public void makeNoise() {
    System.out.println("Some noise");
  }
}

public class Dog extends Animal {
  private boolean canBark;
  
  public Dog
  (String name, int age, boolean canBark) {
    super(name, age);
    this.canBark = canBark;
  }
  
  @Override
  public void makeNoise() {
    if (canBark) {
      System.out.println("Bark bark!");
    } else {
      System.out.println("No barking");
    }
  }
}
```

In questo esempio, la classe `Dog` eredita da `Animal`, il che significa che può usare le variabili `name` e `age` e il metodo `makeNoise()`. Inoltre, `Dog` ha una propria variabile `canBark` e una propria implementazione del metodo `makeNoise()`, che sovrascrive quella presente nella classe padre.

```java
Animal a = new Animal("Fluffy", 5);
a.makeNoise(); // stampa "Some noise"

Dog d = new Dog("Max", 3, true);
d.makeNoise(); // stampa "Bark bark!"
```

### Binding dinamico e Method resolution

In Java (riguardo all'esempio di prima), potrei anche creare una variabile di tipo `Animal` e assegnarle un'istanza di `Dog`:
```java
Animal a = new Dog("Max", 3, true);
a.makeNoise(); // stampa "Bark bark!"
```
ammissibile purché `Dog` sia una sottoclasse di `Animal` (e non il contrario, ad esempio `Dog a = new Animal("Max", 3)` risulta **errato**). In questo caso, `Animal` è il **tipo statico** della variabile `a`, mentre `Dog` è il **tipo dinamico**. <br>
Quando viene invocato il metodo `makeNoise()`, il compilatore non sa quale metodo invocare, poiché non sa quale sia il tipo dinamico della variabile `a` (che viene determinato a runtime). Per questo motivo, Java utilizza il **binding dinamico**.

I passi che segue Java per decidere quale metodo invocare sono i seguenti:

1. Il compilatore controlla se il tipo **statico** della variabile contiene il metodo richiesto (con la stessa signature). Se non è presente, si ha un errore di compilazione. <br> (in questo esempio, Animal ha il metodo `makeNoise()`, quindi si procede al punto 2.).
2. A runtime, Java invece controlla il tipo **dinamico** della variabile. Se questo ha una sua implementazione del metodo richiesto, quella viene utilizzata; altrimenti, si sale lungo la gerarchia delle classi, partendo dal tipo **dinamico**, fino a trovare una classe che ha una implementazione del metodo richiesto (con la stessa signature), o fino a raggiungere la classe del tipo **statico** (che sappiamo contenere per forza il metodo). <br> (in questo esempio, la classe del tipo dinamico `Dog` ha già una sua implementazione di `makeNoise()`, quindi viene scelta quella).
3. Viene invocato il primo metodo trovato.

## `public`, `private`, `protected`, friendly

In Java, ci sono diverse parole chiave che possono essere utilizzate per modificare la visibilità di una classe, di un attributo o di un metodo.

- **`public`**: quando una classe, un attributo o un metodo è dichiarato come `public`, significa che esso è accessibile da qualsiasi altra classe o codice all'interno del programma.
- **`private`**: quando una classe, un attributo o un metodo è dichiarato come `private`, significa che esso è accessibile solo all'interno della classe in cui è dichiarato.
- **`protected`**: quando una classe, un attributo o un metodo è dichiarato come `protected`, significa che esso è accessibile nello stesso package, ma solo all'interno della classe in cui è dichiarato e dalle sottoclassi di quella classe.
- **friendly** (o **`default`**): si dichiara non scrivendo nient'altro, significa che esso è accessibile solo all'interno del package in cui è dichiarato.

## `static` e `final`

- **`static`**: un attributo o un metodo dichiarato come `static` appartiene alla classe e non agli oggetti di quella classe. Ciò significa che non è necessario creare un'istanza della classe per accedere a un attributo statico o chiamare un metodo statico. Ad esempio, si può avere una classe di utilità per la conversione delle temperature, con un attributo statico per la costante del gas perfetto:
```java
public class ConversioneTemperature {
  public static final double 
    COSTANTE_GAS_PERFETTO = 8.3145;

  public static double kelvinToCelsius
  (double temperaturaInKelvin) {
      return temperaturaInKelvin - 273.15;
  }
}

/* Si può quindi accedere all'attributo 
COSTANTE_GAS_PERFETTO e chiamare il metodo 
kelvinToCelsius() senza creare un'istanza 
della classe ConversioneTemperature */
```
---
- **`final`**: quando una classe è dichiarata come `final`, significa che non può essere estesa (cioè, non può avere sottoclassi). Quando un attributo è dichiarato come `final`, significa che ha un valore costante e non può essere modificato una volta assegnato. Quando un metodo è dichiarato come `final`, significa che non può essere sovrascritto da una sottoclasse.

## `abstract` e `interface`

- **`abstract`**: Una classe dichiarata come `abstract` non può essere istanziata (cioè, non puoi creare oggetti da essa). Invece, serve come base per le sottoclassi. Una classe astratta può avere metodi sia astratti che concreti (cioè, con corpo). I metodi astratti devono essere implementati dalle sottoclassi, mentre i metodi concreti possono essere utilizzati direttamente dalle sottoclassi senza alcuna implementazione aggiuntiva. 
<!--
Ad esempio:
```java
public abstract class Animale {
  private String nome;

  public Animale(String nome) {
      this.nome = nome;
  }

  public abstract void emettiSuono();

  public String getNome() {
      return nome;
  }
}
```
-->
- **`interface`**: Un'**interfaccia** è una classe speciale che contiene solo metodi astratti (cioè, senza corpo). Una classe può implementare un'interfaccia (scrivendo `implements`, invece di `extends`) ; per farlo **deve** definirne tutti i metodi. Le interfacce sono spesso utilizzate per definire un contratto a cui le classi devono aderire.

## `this` e `super`

- La parola chiave **`this`** fornisce un riferimento all'oggetto corrente su cui è stato invocato il metodo che stiamo implementando. Può risultare utile quando tale metodo acquisisce dei parametri in input che hanno lo stesso nome di alcuni attributi della classe a cui appartiene: attraverso la keyword `this` possiamo accedere a questi attributi della classe che altrimenti risulterebbero "oscurati" dai parametri. Ad esempio:
```java
public class Persona {
  private String nome;
  private int età;

  public Persona(String nome, int età) {
    /* Assegna i valori di nome e età 
    agli attributi dell'oggetto corrente */
    this.nome = nome;
    this.età = età;
  }

  ...
}
```
Nell'esempio sopra, `this` viene utilizzato nel costruttore per fare riferimento agli attributi dell'oggetto corrente.

- La parola chiave **`super`** si riferisce alla **superclasse** di una sottoclasse. Può essere utilizzata per fare riferimento a metodi e attributi della superclasse all'interno della sottoclasse.
Una delle principali ragioni per cui si utilizza `super` è per chiamare il costruttore della superclasse nel costruttore della sottoclasse. Ciò viene fatto utilizzando la sintassi `super(arg1, arg2, ...)`, dove gli argomenti sono i parametri del costruttore della superclasse.

## Casting ed errori a runtime (`ClassCastException`)

Il **casting** in Java è un'operazione che consiste nel convertire un riferimento di un tipo di dato in un riferimento di un altro tipo di dato. Esistono due tipi di casting:

- **Upcasting**: è la conversione di un riferimento a un tipo di dato più specifico in un riferimento a un tipo di dato più generico. Ad esempio:
```java
String s = new String("Ciao");
Object o = s;
```
In questo esempio, si sta convertendo il riferimento a un oggetto `String` in un riferimento a un oggetto `Object`. L'upcasting viene eseguito in modo implicito e non richiede l'utilizzo delle parentesi tonde. <br>
_Attenzione_: È lecito solo se il tipo di dato al quale si sta convertendo il riferimento è un supertipo del tipo di dato del riferimento originale (per le regole dell'ereditarietà).
- **Downcasting**: è la conversione di un riferimento a un tipo di dato più generico in un riferimento a un tipo di dato più specifico. Ad esempio:
```java
Object o = new String("Ciao");
String s = (String) o;
```
In questo esempio, si sta convertendo il riferimento a un oggetto `Object` in un riferimento a un oggetto `String`. Il downcasting viene eseguito in modo esplicito e richiede l'utilizzo delle parentesi tonde. <br>
_Attenzione_: Può lanciare un'eccezione (errore a runtime) di tipo `ClassCastException` se eseguito impropriamente.

### `ClassCastException`
I cast eseguiti impropriamente possono generare errori a runtime (eccezioni) di tipo `ClassCastException`. Si verificano quando si tenta di convertire un riferimento di un oggetto in un tipo di riferimento che non è compatibile con l'oggetto a cui fa riferimento. <br> Ad esempio, questo può accadere quando si tenta di fare un cast da un oggetto di una classe a un oggetto di una classe figlia, ma l'oggetto non è effettivamente un'istanza della classe figlia. In questo caso, verrà generata un'eccezione di tipo `ClassCastException` a runtime. Ad esempio, in questo codice:
```java
Object o = new Object();
String s = (String) o;
```
l'oggetto `o` non è un'istanza della classe `String`, quindi il cast non è valido e verrà generata un'eccezione di tipo `ClassCastException` a runtime. Per evitare questo tipo di eccezione, è necessario assicurarsi che l'oggetto a cui fa riferimento il riferimento originale sia effettivamente un'istanza della classe a cui si sta tentando di fare il cast. Ad esempio:
```java
Object o = new String("Ciao");
String s = (String) o;
// ok, o è un'istanza di String
```

---

## Collections

Le **Collections** permettono di gestire insiemi di oggetti.

### `List<E>`

La classe **`java.util.List`** è un'interfaccia che rappresenta una lista ordinata di elementi. Ecco i metodi disponibili per questa interfaccia:

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

Le principali implementazioni dell'interfaccia sono `ArrayList` e `LinkedList`.

### `Set<E>`

La classe **`java.util.Set`** è un'interfaccia che rappresenta un insieme di elementi, ovvero una raccolta di elementi **senza duplicati**. Ecco i metodi disponibili per questa interfaccia:

- **`boolean add(E e)`**: aggiunge un elemento all'insieme. Restituisce true se l'elemento viene aggiunto con successo, false altrimenti.
- **`boolean addAll(Collection<? extends E> c)`**: aggiunge tutti gli elementi di una collezione all'insieme. Restituisce true se almeno un elemento viene aggiunto con successo, false altrimenti.
- **`void clear()`**: rimuove tutti gli elementi dall'insieme. Restituisce nulla.
- **`boolean contains(Object o)`**: verifica se l'oggetto specificato è presente nell'insieme. Restituisce true se l'oggetto è presente nell'insieme, false altrimenti.
- **`boolean containsAll(Collection<?> c)`**: verifica se tutti gli elementi di una collezione sono presenti nell'insieme. Restituisce true se tutti gli elementi sono presenti nell'insieme, false altrimenti.
- **`boolean equals(Object o)`**: verifica se l'insieme è uguale a un altro oggetto. Restituisce true se l'oggetto è uguale all'insieme, false altrimenti. _Attenzione_: anche qui, se l'oggetto passato è un Set, allora viene verificato se l'insieme è equivalente a quello passato per parametro.
- **`int hashCode()`**: restituisce il codice hash per l'insieme.
- **`boolean isEmpty()`**: verifica se l'insieme è vuoto. Restituisce true se l'insieme è vuoto, false altrimenti.
- **`Iterator<E> iterator()`**: restituisce un iteratore per l'insieme.
- **`boolean remove(Object o)`**: rimuove l'oggetto specificato dall'insieme. Restituisce true se l'oggetto viene rimosso con successo, false altrimenti.
- **`boolean removeAll(Collection<?> c)`**: rimuove dall'insieme tutti gli elementi presenti in una collezione. Restituisce true se almeno un elemento viene rimosso con successo, false altrimenti.
- **`boolean retainAll(Collection<?> c)`**: rimuove dall'insieme tutti gli elementi che non sono presenti in una collezione. Restituisce true sse almeno un elemento viene rimosso con successo.
- **`int size()`**: restituisce il numero di elementi presenti nell'insieme.
- **`Object[] toArray()`**: restituisce un array di oggetti contenente tutti gli elementi dell'insieme.
- **`<T> T[] toArray(T[] a)`**: restituisce un array di tipo specificato contenente tutti gli elementi dell'insieme.

---

La principale implementazione dell'interfaccia è `HashSet`.

Un metodo importante ereditato da Object e che viene ridefinito allo stesso modo dalle implementazioni precedenti di List e Set è **`String toString()`**: data una Lista/Set di elementi A, B, ..., F restituisce "[A.toString(), B.toString(), ..., F.toString()]".

### Iterare su un insieme

Per iterare su un insieme (classe `Set`), si può utilizzare il metodo **`iterator()`** della classe `Set`. Questo metodo restituisce un'istanza dell'interfaccia `Iterator`, che permette di scorrere gli elementi dell'insieme uno alla volta.
Ecco un esempio di come utilizzare l'iteratore per stampare gli elementi di un insieme:

```java
Set<String> set = new HashSet<>();
// aggiungi elementi al set

// otteniamo un iteratore per l'insieme
Iterator<String> iterator = set.iterator();

/* utilizziamo l'iteratore 
per scorrere gli elementi dell'insieme */
while (iterator.hasNext()) {
  /* il metodo next() restituisce l'elemento 
  corrente e sposta l'iteratore 
  all'elemento successivo */
  String element = iterator.next();
  System.out.println(element);
}
```

In questo esempio, viene creato un insieme di stringhe e viene inizializzato un iteratore per l'insieme utilizzando il metodo `iterator()`. Quindi, all'interno del ciclo while, il metodo `hasNext()` viene utilizzato per verificare se ci sono ancora elementi da scorrere nell'insieme. Se ci sono ancora elementi, il metodo `next()` restituisce l'elemento corrente e sposta l'iteratore all'elemento successivo, quindi viene stampato a schermo.

È importante notare che il metodo `next()` può lanciare un'eccezione `NoSuchElementException` se l'iteratore è alla fine dell'insieme e non ci sono più elementi da scorrere. Per questo motivo, è consigliabile utilizzare il metodo `hasNext()` per verificare se ci sono ancora elementi prima di chiamare `next()`.

Inoltre, l'interfaccia `Iterator` fornisce altri metodi utili per la gestione dell'iterazione, come ad esempio:

- `remove()`: rimuove l'elemento corrente dall'insieme. Questo metodo può essere chiamato solo dopo che `next()` è stato chiamato per restituire l'elemento corrente. Lancerà un'eccezione `IllegalStateException` se viene chiamato prima di `next()` o dopo che `hasNext()` restituisce false.
- `forEachRemaining(Consumer<? super E> action)`: esegue un'azione specificata per ogni elemento rimanente nell'iteratore. Questo metodo è utile quando si vuole eseguire un'azione per ogni elemento dell'insieme senza dover gestire manualmente l'iterazione.

Ecco un esempio di come utilizzare questi metodi per rimuovere gli elementi pari dall'insieme:

```java
Set<Integer> set = new HashSet<>(Arrays
  .asList(1, 2, 3, 4, 5));

Iterator<Integer> iterator = set.iterator();
while (iterator.hasNext()) {
  int element = iterator.next();
  if (element % 2 == 0) {
    iterator.remove();
  }
}

/* il set ora contiene solo elementi dispari: 
[1, 3, 5] */
```

### `Map<K,V>`

La classe **`java.util.Map`** è un'interfaccia che rappresenta una mappa di chiavi (di tipo K) a valori (di tipo V). Ecco i metodi disponibili per questa interfaccia:

- **`void clear()`**: rimuove tutte le coppie chiave-valore dalla mappa. Restituisce nulla.
- **`boolean containsKey(Object key)`**: verifica se la chiave specificata è presente nella mappa. Restituisce true se la chiave è presente nella mappa, false altrimenti.
- **`boolean containsValue(Object value)`**: verifica se il valore specificato è presente nella mappa. Restituisce true se il valore è presente nella mappa, false altrimenti.
- **`Set<Map.Entry<K,V>> entrySet()`**: restituisce un insieme di tutte le coppie chiave-valore presenti nella mappa.
- **`V get(Object key)`**: restituisce il valore associato alla chiave specificata nella mappa. Restituisce null se la chiave non è presente nella mappa.
- **`boolean isEmpty()`**: verifica se la mappa è vuota. Restituisce true se la mappa è vuota, false altrimenti.
- **`Set<K> keySet()`**: restituisce un insieme di tutte le chiavi presenti nella mappa.
- **`V put(K key, V value)`**: aggiunge una coppia chiave-valore alla mappa o sostituisce il valore associato alla chiave specificata se già presente. Restituisce il valore precedentemente associato alla chiave, oppure null se la chiave non era presente nella mappa.
- **`void putAll(Map<? extends K,? extends V> m)`**: aggiunge tutte le coppie chiave-valore di un'altra mappa alla mappa corrente. Restituisce nulla.
- **`V remove(Object key)`**: rimuove la coppia chiave-valore associata alla chiave specificata dalla mappa. Restituisce il valore associato alla chiave, oppure null se la chiave non era presente nella mappa.
- **`int size()`**: restituisce il numero di coppie chiave-valore presenti nella mappa.
- **`Collection<V> values()`**: restituisce una collezione di tutti i valori presenti nella mappa.

Le principali implementazioni di Map sono `HashMap`, `LinkedMap` e `TreeMap`. Si noti come nella prima implementazione non è definito un ordine tra elementi, nella seconda l'ordine è quello di inserimento e nella terza l'ordine ASCII tra chiavi. 

Data una Map di elementi (kA,A), (kB,B), ..., (kF,F) il metodo **`String toString()`** delle implementazioni restituisce "{kE.toString():E.toString(), kB.toString():B.toString(), ..., kC.toString():C.toString()}" nell'ordine stabilito.

---

### Arrays

Un array di elementi E viene dichiarato e inizializzato nel seguente modo:

```java
//dichiarazione
E[] anArray;
//inizializzazione
anArray = new E[SIZE];
//inizializzazione di un certo elemento
anArray[INDEX] = new E();
//dichiarazione di un array bidimensionale
E[][] a2dimArray;
//inizializzazione di un array bidimensionale
a2dimArray = new E[SIZE1][SIZE2];
//dichiarazione e inizializzazione
//di un array di interi
int[] intArray = {0, 4, 3, -2};
```

Si noti come con la prima istruzione viene allocato solamente lo spazio per un riferimento sullo stack, con la seconda lo spazio per SIZE riferimenti sullo heap e con la terza lo spazio per un oggetto E sullo heap. Nel caso di array di tipi primitivi, nella seconda istruzione viene invece allocato spazio sullo heap per contenere SIZE elementi, la terza istruzione (sostituendo new E() con il valore dell'elemento) non alloca quindi spazio in memoria.

Gli array hanno un attributo pubblico **`int length`** che contiene la lunghezza dell'array.

Il metodo **`String toString()`**, applicato su un array di elementi A, B, ..., F restituisce "{A.toString(), B.toString(), ..., F.toString()}".
