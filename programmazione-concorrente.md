# Programmazione concorrente

La programmazione concorrente permette di svolgere più attività (dette task) in maniera simultanea. 

L'esecuzione può avvenire in parallelismo fisico (ovvero mediante l'utilizzo di più processori o un 
processore multi-core) o mediante la condivisione di un unico processore, seguendo le decisioni dello 
scheduler (sistemi time-shared).

Si può avere concorrenza:
- A livello di processi: ogni processo ha un suo spazio di memoria riservato, la comunicazione fra di
  essi deve avvenire mediante meccanismi di [IPC (Inter-process communication)](https://en.wikipedia.org/wiki/Inter-process_communication). Non è argomento del corso.
- A livello di **thread**: un singolo processo può contenere numerosi thread, che condividono tutti lo
  stesso [spazio di indirizzamento](https://en.wikipedia.org/wiki/Address_space) e possono comunicare 
  mediante variabili condivise.

La libreria standard Java mette a disposizione, oltre alla primitiva di sistema Thread, anche una serie
di primitive per semplificare la programmazione concorrente.

## Thread

Per creare un thread, è sufficiente estendere la classe `java.lang.Thread`, fare l'override del metodo `run()`,
istanziare la classe e chiamare il metodo `start()` (**NB: start, non run**):
```java
class MyThread extends Thread {
  @Override
  public void run() {
    // Fai cose
  }
}
...
 // Fa partire il thread e ritorna subito
new MyThread().start();
```

Per motivi di riutilizzo del codice, viene solitamente preferito utilizzare un metodo alternativo per la creazione di
un Thread, implementando invece l'interfaccia `java.lang.Runnable`:
```java
class MyRunnable implements Runnable {
  @Override
  public void run() {
    // Fai cose
  }
}
...
// Fa partire il thread e ritorna subito
new MyThread(new MyRunnable()).start();
```


Notiamo come, in entrambi i casi, il thread sia libero di accedere a qualsiasi variabile globale o passata nel costruttore,
causando potenzialmente errori di interferenza se più thread accedono alle stesse variabili contemporaneamente.

## Intrinsic lock

Java, di default, associa a ogni oggetto un proprio "lock", ovvero un oggetto che permette di implementare mutua esclusione tra
i vari thread su sezioni di codice di interesse. Questo avviene mediante l'uso della keyword `synchronized`, specificando poi
l'oggetto di cui si vuole utilizzare il lock:
```java
class Account {
  private float balance;

  public Account(float balanceIniz) { 
    balance = balanceIniz; 
  }
  
  public void deposit(float money) { 
    synchronized(this) { 
      balance += money; 
    }
  }
  public void withdraw(float money) {
    synchronized(this) {
      balance -= money; 
    }
  }
}
```

L'intrinsic lock:
- mette in mutua esclusione sezioni di codice, permettendo a un solo thread alla volta
  l'esecuzione, sospendendo gli altri thread chiamanti fino al completamento.
- é un lock rientrante: se il thread, quando raggiunge una sezione critica, è già in
  possesso del lock, continuerà la sua esecuzione senza venire sospeso.
- quando viene acquisito/rilasciato, forza la sincronizzazione della cache locale del thread con 
  la memoria centrale, garantendo che tutte le variabili lette siano aggiornate.

Notiamo come, a causa della cache locale del thread menzionata al terzo punto, sia necessario
mettere in sezioni sincronizzate anche metodi che leggono solo una variabile, senza modificarla.
Questo perché, sebbene il metodo stesso non la modifichi, la variabile potrebbe però essere
cambiata esternamente da altri thread, causando un desync tra la cache locale e la memoria centrale.

Esiste anche una forma più breve di scrivere il codice precedente, mettendo la keyword
direttamente sul metodo:
```java
class Account {
  private float balance;

  public Account(float balanceIniz) { 
    balance = balanceIniz; 
  }
  
  public synchronized void deposit(
    float money) { 
    balance += money; 
  }

  public synchronized void withdraw(
    float money) {
    balance -= money; 
  }
}
```

---

E' possibile chiamare il metodo `synchronized` su qualsiasi oggetto di cui si ha una referenza 
(quindi escludendo i primitivi):
```java
class Account {
  private float balance;
  private final Object lock = new Object();
  ...  
  public void deposit(float money) { 
    synchronized(lock) { 
      balance += money; 
    }
  }
  public void withdraw(float money) {
    synchronized(lock) {
      balance -= money; 
    }
  }
}
```

Questo si rivela molto utile per evitare di
[sincronizzare eccessivamente](https://github.com/HugoMatilla/Effective-JAVA-Summary#70-document-thread-safety), 
andando a ridurre il parallelismo tra i thread (cosa che nei TdE solitamente è richiesta).
Si veda per esempio l'esercizio svolto sotto, dove si ha un'intera array di locks invece di
utilizzare unicamente il singolo lock di `this`;
<!--
Aggiungo che questa forma è solitamente sconsigliata anche perché usa in automatico l'intrinsic lock di `this`, che
permette all'utilizzatore di acquisire egli stesso il lock](https://stackoverflow.com/a/7513271),
andando potenzialmente a poter interferire con lo stato interno di un oggetto, causando deadlocks, etc.
--> 

Altre cose su cui riporre particolare attenzione quando si utilizza un intrinsic lock:
- essendo il lock legato ad un'instanza di una classe, quando si utilizza `synchronized` in metodi statici non si ha a disposizione
  un istanza su cui sincronizzare. Si utilizza quindi l'istanza della classe stessa, ovvero:
```java
public class ExampleClass {
  public static void static1() {
    synchronized(ExampleClass.class) {
      // sezione critica
    }
  }
  
  // Di default Java effettua la stessa 
  // cosa anche per  synchronized posto 
  // su un metodo statico
  // I due metodi sono equivalenti
  public static synchronized void static2() {
    // sezione critica
  }
}
```
- `synchronized` posto su un metodo non sarà automaticamente ereditato da metodi che ne effettuano l'overriding.
  Bisognerà quindi richiedere esplicitamente che anche il l'overriding method sia synchronized.

## Variabili volatili e variabili atomiche

Se non necessitiamo di una sezione critica, ma solo di forzare la sincronizzazione di una 
variabile della cache locale del thread con la memoria centrale, possiamo utilizzare la keyword `volatile`
sulla variabile di interesse:
```java
class StudentGrade {
  private final String matricola;
  private volatile int grade;

  public StudentGrade(String matricola) {
    this.matricola = matricola;
  }

  public void getGrade() {
    return grade;
  }

  public void setGrade(int grade) {
    this.grade = grade;
  }
}
```

Lo svantaggio è la mancanza della sezione critica stessa: un'operazione come `x++` non è atomica, e se non sincronizzata
causerà problemi a prescindere dalla presenza di volatile. 
Questo problema viene risolto dall'utilizzo delle variabili atomiche, che sono implementate dalle classi 
`AtomicBoolean`, `AtomicInteger`, `AtomicLong` e `AtomicReference<V>`.
```java
class Counter {
  private final AtomicInteger count = 
      new AtomicInteger();

  public int get() {
    return count.get();
  }

  public void increment() {
    count.getAndIncrement();
  }

  public void set(int count) {
    count.getAndSet(count);
  }
}
```

La mancanza di un tipo atomico per double e float può essere sopperita mediante:
- float: AtomicInteger con i metodi `Float.floatToIntBits(float)` e `Float.intBitstoFloat(int)`
- double: AtomicLong con i metodi `Double.doubleToLongBits(double)` e `Double.longBitsToDouble(long)`

oppure, se è necessario sommare, utilizzando `DoubleAdder`:
```java
class Account {
  private final DoubleAdder balance =
      new DoubleAdder();
  
  public float get() { 
    return (float) balance.sum(); 
  }
  
  public void deposit(float money) { 
    balance.add(money); 
  }

  public void withdraw(float money) {
    balance.add(-money); 
  }
}
```

Particolare attenzione va posta anche nella dichiarazione di array:
`volatile int[] array = new int[20]` dichiara un array di interi con referenza volatile, _non_ un array di 
interi volatili. Bisogna quindi utilizzare `AtomicIntegerArray`, `AtomicLongArray` o `AtomicReferenceArray<E>`.

<!--
Anche se non richiesto dal corso, il vantaggio di usare questo tipo di variabili invece di un lock
(intrinseco o esplicito che sia) è che, sebbene volatile disattivi alcune ottimizzazioni del compilatore,
un lock fa partire tutto il meccanismo di lifecycle del thread, che all'effettivo è nettamente più lento
-->

---

## Variabili finali e oggetti immutabili

Le variabili finali non hanno bisogno di essere sincronizzate in alcuna maniera, in quanto, non potendo cambiare,
è impossibile che avvenga un desync tra la cache locale e la memoria centrale.

Questo ci porta agli oggetti immutabili: un oggetto si dice **immutabile** se ogni suo campo è dichiarato `final` 
e ogni modifica dello stesso avviene mediante la creazione di un nuovo oggetto:
```java
public class ImmutableRGB {
  private final String name;
  // Values must be between 0 and 255.
  private final int red;
  private final int green;
  private final int blue;

  private int check(int component) {
    if (component < 0 || component > 255)
      throw new 
        IllegalArgumentException();
    return component;
  }
  
  public ImmutableRGB(int r, int g, int b, 
                String name) {
    this.red = check(r);
    this.green = check(g);
    this.blue = check(b);
    this.name = name;
  }

  public int getRGB() {
    return 
      (red << 16) | (green << 8) | blue;
  }
  public String getName() {
    return name;
  }
  public ImmutableRGB invert() {
    return new ImmutableRGB(255 - red, 
            255 - green, 
            255 - blue, 
            "Inverse of " + name);
  }
}
```

Gli oggetti immutabili non necessitano di alcun tipo di sincronizzazione.

## `wait`, `notify` e `notifyAll` (producer/consumer pattern)

Java mette a disposizione nell'intrinsic lock anche delle primitive per implementare dei **Guarded Blocks**,
ovvero delle condizioni che devono essere vere prima che l'esecuzione di un metodo possa continuare:
- `wait() throws InterruptedException`: sospende l'esecuzione di un thread fino a quando viene risvegliato da un altro,
  rilasciando il lock al momento della sospensione e ri-acquisendolo al risveglio
- `notify()`: sveglia un thread sospeso in attesa sul lock di questo oggetto per riprendere la sua esecuzione
- `notifyAll()`: sveglia tutti i thread sospesi in attesa sul lock di questo oggetto

L'invocazione di questi metodi richiede che il thread invocante sia possessore del lock stesso.

Notiamo inoltre come il metodo wait sollevi l'eccezione `InterruptedException`, che avviene se il thread corrente viene
interrotto (ad esempio perché viene richiesta la terminazione del programma).

Riprendendo l'esempio di un account bancario, se volessimo aspettare che l'utente abbia soldi prima di effettuare
un'operazione di prelievo:
```java
class Account {
  private final Object lock = new Object();
  private float balance;

  public Account(float balanceIniz) {
    balance = balanceIniz;
  }
  
  public void deposit(float money) { 
    synchronized(lock) {
      balance += money;
      lock.notifyAll();
    }
  }

  public void withdraw(float money) 
        throws InterruptedException {
    synchronized(lock) {
      // Notiamo l'utilizzo del while 
      // al posto di un if: questo 
      // perché il thread potrebbe 
      // svegliarsi spontaneamente 
      // (su alcune architetture 
      //  e/o OS specifici)
      while (balance - money < 0) 
        lock.wait();
      balance -= money;
    }
  }
}
```

<!--
Nota: l'utilizzo di queste primitive (specialmente in modo diverso da sopra) è solitamente 
sconsigliato in quanto essendo un API molto low-level 
[è molto facile sbagliare](https://github.com/HugoMatilla/Effective-JAVA-Summary#69-prefer-concurrency-utilities-to-wait-and-notify)
e non ottenere l'effetto desiderato.
-->

## Explicit lock

Meccanismi di lock più sofisticati sono forniti dal package `java.util.concurrent.locks`. Questo definisce un'interfaccia
di base `Lock` che, oltre a permettere le stesse operazioni dell'intrinsic lock, aggiunge anche ulteriori metodi e funzionalità:
- Permette di chiamare `lock` e `unlock` anche in metodi separati
- Il lock è sempre esplicito, bisogna per forza pensare a chi ne avrà accesso
- `lockInterruptibly() throws InterruptedException`: esegue la stessa operazione di lock, ma permette di interrompere 
   l'esecuzione del thread quando questo è stato sospeso.
- `boolean tryLock()`: acquisisce il lock solo se non è già utilizzato
```java
Lock lock = new ReentrantLock();
if (lock.tryLock()) {
  try {
    // qui siamo in sezione critica
  } finally {
    // 'finally' per rilasciare il lock 
    // qualsiasi cosa succeda, sia 
    // esecuzione normale che eccezioni
    lock.unlock();
  }
} else {
  // azioni alternative dove il 
  // lock non è necessario
}
```

---

## Executors

L'utilizzo eccessivo/non limitato di thread può portare a problemi di performance. Per ovviare a questo problema,
sono state introdotte le interfacce `Executor`, `ExecutorService` e `ScheduledExecutorService` e i metodi statici
nella classe `Executors` per istanziarne implementazioni concrete. Per esempio `Executors.newFixedThreadPool(int)`
utilizza un numero fisso di thread a cui fare eseguire le task.
```java
ExecutorService executor = 
  Executors.newFixedThreadPool(5);
executor.submit(() -> {
  // Questo viene eseguito 
  // su uno dei 5 thread
  System.out.println("Executed on " + 
      Thread.currentThread());
});
```

## Collezioni concorrenti

Sempre il package `java.util.concurrent` introduce anche dei tipi di collezioni che sono già predisposte 
all'utilizzo concorrente, senza necessitare di sincronizzazione. Di seguito una per tipo di collezione:
- `CopyOnWriteArrayList<E>` implementa `List<E>`
- `ConcurrentHashMap<K, V>` implementa `ConcurrentMap<K, V>` che implementa `Map<K, V>`
- `ConcurrentHashMap.<K>newKeySet()` implementa `Set<K>`
- `ConcurrentLinkedQueue` implementa `Queue<E>` (in maniera non bloccante)
- `ArrayBlockingQueue` implementa `BlockingQueue<E>` che implementa `Queue<E>` (aggiungendo operazioni bloccanti)

---

## Esercizio (TdE del 2022-07-21, esercizio 2 - punto a e b)

### Testo dell'esercizio

Si consideri la seguente classe `ScoreBoard` per memorizzare i voti di un insieme di studenti passato in
fase di costruzione:
```java
public class ScoreBoard {
  private String[] students;
  private int[] scores;

  public ScoreBoard(String[] stud) {
    students = new String[stud.length];
    for(int i = 0; i < stud.length; i++) 
      students[i] = stud[i];
    scores = new int[stud.length];
  }

  public int getScore() {
    for(int i = 0; 
      i < students.length; i++) {
      if(students[i].equals(stud)) 
        return scores[i];
    }
    return -1;
  }

  public int setScore(String stud, 
                      int score) {
    for(int i = 0; 
      i < students.length; i++) {
      if(students[i].equals(stud)) 
        scores[i] = score;
    }
  }
}
```

#### Domanda a)

Si introduca l'opportuno codice di sincronizzazione nei metodi `getScore` e `setScore` al fine di massimizzare il
parallelismo, consentendo a thread diversi di accedere in parallelo ai dati di studenti diversi, evitando 
conflitti nell'accesso ai dati (voto) del medesimo studente. 

#### Soluzione

Osserviamo per prima cosa come, non potendo cambiare né il costruttore né la definizione dei campi, possiamo 
scartare a priori variabili volatili e atomiche. Siamo quindi obbligati ad utilizzare intrinsic locking (strano).

Come seconda osservazione, notiamo come students sia inizializzata nel costruttore e non sia poi più modificata.
Questo vuol dire che, molto probabilmente, l'accesso a questa non dovrà stare in sezione critica.

Come ultima cosa, per massimizzare il parallelismo, dobbiamo evitare il conflitto dei dati tra medesimi studenti,
non tra studenti diversi: non dobbiamo quindi utilizzare lo stesso lock per ogni studente, dovremmo avere un lock
per studente. Non potendo dichiarare nessun campo aggiuntivo, possiamo riutilizzare come intrinsic lock i valori 
dentro all'array students, in quanto come detto in precedenza non vengono modificati.
```java
public class ScoreBoard {

  ...

  public int getScore() {
    for(int i = 0; 
      i < students.length; i++) {
      if(students[i].equals(stud)) {
        synchronized(students[i]) {
          return scores[i];
        }
      }
    }
    return -1;
  }

  public int setScore(String stud, 
                int score) {
    for(int i = 0; 
      i < students.length; i++) {
      if(students[i].equals(stud)) {
        synchronized(students[i]) {
          scores[i] = score;
        }
      }
    }
  }
}
```

#### Domanda b)

Si modifichi il metodo `getScore` affinché sospenda il chiamante se il voto dello studente
cercato è minore o uguale a zero. Si specifichi se e come sia necessario modificare altri
metodi.

#### Soluzione

Questo è un esempio di consumer/producer standard:
- La condizione di wait sarà scores[i] <= 0
- Bisogna modificare `setScore` per notificare l'avvenuta modifica
```java
public class ScoreBoard {

  ...

  public int getScore() {
    for(int i = 0; 
      i < students.length; i++) {
      if(students[i].equals(stud)) {
        synchronized(students[i]) {
          while(scores[i] <= 0)
            students[i].wait();
          return scores[i];
        }
      }
    }
    return -1;
  }

  public int setScore(String stud, 
                int score) {
    for(int i = 0; 
      i < students.length; i++) {
      if(students[i].equals(stud)) {
        synchronized(students[i]) {
            scores[i] = score;
            students[i].notifyAll();
        }
      }
    }
  }
}
```
