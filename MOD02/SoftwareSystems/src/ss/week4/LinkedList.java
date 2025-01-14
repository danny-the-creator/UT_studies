package ss.week4;

public class LinkedList<E> {

    private int size;
    private Node first;

    //@ ensures size == 0 && first == null;
    public LinkedList () {
        size = 0;
        first = null;
    }

    //@ requires index >= 0 && index <= size;
//    @ ensures size = old(size) + 1;
    public void add(int index, E element) {
        Node newNode = new Node(element);
        if (index == 0) {
            newNode.next = first;
            first = newNode;
        } else {
            Node p = getNode(index-1);
            newNode.next = p.next;
            p.next = newNode;
        }
        size = size + 1;
    }

    /**
     * @param element the element to remove
     */
    public void remove(E element) {
         // TODO: implement, see exercise P-4.5
    }

    public Node findBefore(E element) {
     // TODO: implement, see exercise P-4.5
        return null;
    }

    /**
     * @param index the index to get the element at
     * @return the element at index index
     */
    //@ requires index >= 0 && index < size;
    public E get(int index) {
        Node p = getNode(index);
        return p.element;
    }

    /**
     * @param i the index to get the Node at
     * @return the Node at index i
     */
    //@ requires i >= 0 && i < size;
    private Node getNode(int i) {
        Node p = first;
        int pos = 0;
        while (pos != i) {
            p = p.next;
            pos = pos + 1;
        }
        return p;
    }

    /**
     * @return the size of the list
     */
    //@ ensures \result >= 0;
    public int size() {
        return size;
    }

    public class Node {
        private E element;
        public Node next;

        public Node(E element) {
            this.element = element;
            this.next = null;
        }

        public E getElement() {
            return element;
        }
    }
}
