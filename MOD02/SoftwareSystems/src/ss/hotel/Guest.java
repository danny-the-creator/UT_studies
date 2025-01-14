/**
 * The Guest class represents a hotel guest who can check in and check out of a room.
 * Each guest has a name and may be associated with a room.
 *
 * @invariant The guest's room is either null (if the guest is not checked in) or has a reference to the guest.
 */
package ss.hotel;

public class Guest {
    /** The name of the guest. */
    private String guest;

    /** The room assigned to the guest. */
    private Room room;

    /**
     * Constructs a Guest object with the specified name.
     *
     * @param name The name of the guest.
     * @return no
     * @ensures The created Guest object has the specified name, and the room is initially null.
     * @require: class Guest, appropriate String input
     * @ensure: the Guest name creation
     */

    public Guest(String name) {
        this.guest = name;
    }
    @Override
    public String toString(){
        return "Guest "+ this.guest;
    }

    /**
     * Retrieves the name of the guest.
     * @param
     * @return The name of the guest.
     * @require: Guest classes implemented
     * @ensure: the Guest's name is being returned correctly
     */
    //@pure
    public String getName() {
        return guest;
    }

    /**
     * Retrieves the room associated with the guest.
     * @param
     * @return The room associated with the guest, or null if the guest is not checked in.
     * @require: Room and Guest classes implemented
     * @ensure: The room number is being return correctly
     *
     */
    //@ pure
    public Room getRoom() {
        return room;
    }

    /**
     * Attempts to check in the guest to the specified room.
     *
     * @param room The room to check in.
     * @return True if the check-in is successful, false otherwise (e.g., if the guest is already checked in or the room is occupied).
     */
    //@ requires room != null && room.getGuest() == null && (this.room == null);
    //@ ensures \result == true ==> this.room == room && room.getGuest() == this;
    //@ ensures \result == false ==> this.room == \old(this.room) && room.getGuest() == \old(room.getGuest());
    public boolean checkin(Room room) {
        if ((this.room != null) || (room.getGuest() != null)) {
            return false;
        }
        this.room = room;
        this.room.setGuest(Guest.this);
        return true;
    }

    /**
     * Attempts to check out the guest from the current room.
     * @param
     * @return True if the check-out is successful, false otherwise (e.g., if the guest is not currently checked in).
     */
    //@ requires this.room != null;
    //@ ensures \result == true ==> this.room == null && room.getGuest() == null;
    //@ ensures \result == false ==> this.room == \old(this.room) && room.getGuest() == \old(room.getGuest());
    public boolean checkout() {
        if (room == null) {
            return false;
        }
        this.room.setGuest(null);
        this.room = null;
        return true;
    }
}