package ss.week4;

public class DoublyLinkedList<Element> {

    private /*@ spec_public @*/ int size;
    private Node head;
    private Node first;

    //@ ensures this.size == 0;
    //@ ensures get(0) == null;
    public DoublyLinkedList() {
        size = 0;
        head = new Node(null);
        head.next = head;
        head.previous = head;
    }

    //@ requires element != null;
    //@ requires 0 <= index && index <= this.size;
    //@ ensures this.size == \old(size) + 1;
    //@ ensures this.get(index).equals(element);
    /*@ ensures (\forall int j; 0 <= j && j < index;
                         \old(this.get(j)).equals(this.get(j))); */
    /*@ ensures (\forall int j; index <= j && j < \old(size);
                         \old(this.get(j)).equals(this.get(j + 1))); */
    public void add(int index, Element element) {

        Node elem = new Node(element);
        Node old = getNode(index);
        elem.previous = old.previous;
        elem.next = old;
        elem.previous.next = elem;
        elem.next.previous = elem;
        size = size +1;
    }

    //@ requires 0 <= index && index < this.size;
    //@ ensures this.size == \old(size) - 1;
    /*@ ensures (\forall int j; 0 <= j && j < index;
                         \old(this.get(j)).equals(this.get(j))); */
    /*@ ensures (\forall int j; index <= j && j < this.size;
                         this.get(j).equals(\old(this.get(j + 1)))); */
    public void remove(int index) {
        Node prev = getNode(index-1);
        Node next = getNode(index+1);
        prev.next = next;
        next.previous = prev;
        size = size -1;
    }

    //@ requires 0 <= index && index < this.size;
    public Element get(int index) {
        Node p = getNode(index);
        return p.element;
    }

    /**
     * Gets the node containing the element with the specified index.
     * This is the head node if the specified index is -1 or this.size.
     */
    //@ requires -1 <= i && i <= this.size;
    private Node getNode(int i) {
        Node p = head;
        if (i > size / 2) {
            int pos = size;
            while (pos > i) {
                p = p.previous;
                pos = pos - 1;
            }
        } else {
            int pos = -1;
            while (pos < i) {
                p = p.next;
                pos = pos + 1;
            }
        }
        return p;
    }

    //@ ensures /result >= 0;
    public /*@ pure */ int size() {
        return this.size;
    }

    private class Node {
        public Node(Element element) {
            this.element = element;
            this.next = null;
            this.previous = null;
        }

        private Element element;
        public Node next;
        public Node previous;

        public Element getElement() {
            return element;
        }
    }
}
