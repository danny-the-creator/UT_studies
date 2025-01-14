package ss.hotel;

import static org.junit.jupiter.api.Assertions.assertEquals;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

public class RoomTest {
    private Guest guest;
    private Room room;

    private Safe safe;

    @BeforeEach
    public void setUp() {
        room = new Room(101);
        guest = new Guest("Jip");
        safe = room.getSafe();
         // TODO: initialise the variable room
    }

    @Test
    public void testSetUp() {
        assertEquals(101, room.getNumber());
    }

    @Test
    public void testSetGuest() {
        room.setGuest(guest);
        assertEquals(guest, room.getGuest());
    }

    @Test
    public void testSafe() {
        assertEquals(safe, room.getSafe());
    }
}
