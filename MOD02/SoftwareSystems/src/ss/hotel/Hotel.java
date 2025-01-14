package ss.hotel;

/**
 * The Hotel class.
 */
public class Hotel {
    protected String name;
    protected Room[] rooms;

    public String getName() {
        return this.name;
    }

    public Hotel(String hotelName) {
        this.name = hotelName;
        this.rooms = new Room[2];
        rooms[0] = new Room(101);
        rooms[1] = new Room(102);
    }

    /**
     * Check a guest in a free room if there is not already a guest with this name.
     *
     * @param guestName The name of the guest.
     * @return Room object with a guest of the given name checked in,
     * null in case there is already a guest with this name or the hotel is full.
     */
    //@ requires guestName != null;
    //@ ensures (\result == null) <==> (getRoom(guestName) != null && getRoom(guestName).getGuest().getName().equals(guestName));
    public Room checkIn(String guestName) {
        if (this.getRoom(guestName) != null || this.getFreeRoom() == null) {
            return null;
        }
        Room freeRoom = this.getFreeRoom();
        Guest guest = new Guest(guestName);
        guest.checkin(freeRoom);
        return freeRoom;
        // If the hotel is full, return null
    }

    //@ ensures \result == (\old(getRoom(name)) != null && \old(getRoom(name)).getGuest() != null && \old(getRoom(name)).getGuest().getName().equals(name));
    public boolean checkOut(String name) {
        if (getRoom(name) != null && getRoom(name).getGuest() != null && getRoom(name).getGuest().getName().equals(name)) {
            getRoom(name).getSafe().deactivate();
            getRoom(name).getGuest().checkout();
            return true;
        }
        return false;
    }

    //@ ensures (\result instanceof Room) || (\result == null);
    //@ pure
    public Room getFreeRoom() {
        for (int i = 0; i < rooms.length; i++) {
            if (rooms[i].getGuest() == null) {
                return rooms[i];
            }
        }
        // If there is no free room available.
        return null;
    }

    //@ ensures (\result == null) || (\result.getGuest().getName().equals(guestName));
    //@ pure
    public Room getRoom(String guestName) {
        for (int i = 0; i < rooms.length; i++) {
            if (rooms[i].getGuest() != null && rooms[i].getGuest().getName().equals(guestName)) {
                return rooms[i];
            }
        }
        // Return null if the guest cannot be found in any room.
        return null;
    }

    public String toString() {
        String allRooms = "";
        String allGuests = "";
        String allSafes = "";
        String returnedString = "";
        for (Room room : this.rooms) {
            allRooms = "Room " + room.getNumber() + "\n";
            if (room.getGuest() != null) {
                allGuests = "rented by: " + room.getGuest().toString() + "\n";
            } else {
                allGuests = "rented by: null\n";
            }
            String active = room.getSafe().isActive() ? "true" : "false";
            allSafes = "safe active: " + active + "\n";
            returnedString += allRooms + allGuests + allSafes;
        }
        return returnedString;
    }
}