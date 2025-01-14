package ss.hotel;

import ss.hotel.bill.Bill;
import ss.hotel.bill.BillPrinter;

public class PricedHotel extends Hotel{
    public static final double ROOM_PRICE = 50;
    public static final double SAFE_PRICE = 12.5;
    private Bill bill_for_night;
    public PricedHotel(String hotelName) {
        super(hotelName);
//        super.rooms = new Room[2];
        rooms[0] = new PricedRoom(101, ROOM_PRICE, SAFE_PRICE);
        rooms[1] = new Room(102);

    }
    //@ requires guestName!= null;
    public Bill getBill(String guestName, int nNights, BillPrinter bill){
        for (Room room : rooms) {
            if (room.getGuest() != null && room.getGuest().getName().equals(guestName) && room instanceof PricedRoom) {
                bill_for_night = new Bill(bill);
                for (int i = 1; i<=nNights; i++){
                    bill_for_night.addItem((PricedRoom) room);
                }

                if (room.getSafe().isActive()){
                    bill_for_night.addItem((PricedSafe)room.getSafe() );
                }
                bill_for_night.close();
                return bill_for_night;
            }
        }
        return null;
    }

}
