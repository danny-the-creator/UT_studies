package ss.hotel;

public class Safe {
    //@public invariant isOpened() ==> isActive();

    private boolean safe;
    public boolean active;
    public boolean opened;
    public Safe() {
        active = false;
        opened = false;
    }
    public void activate(){
        active = true;
    }
    public void deactivate(){
        close();
        active = false;
    }
    public void open(){
        opened = true;
    }
    public void close(){
        opened = false;
    }

    public boolean isActive() {
        return active;
    }
    public boolean isOpened() {
        return opened;
    }
}
