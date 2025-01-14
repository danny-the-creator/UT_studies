/**
 * Handles the DOMContentLoaded event, which initializes the calendar with mock homework data.
 */
document.addEventListener('DOMContentLoaded', function() {
    /**
     * Fetches mock homework data.
     * @returns {Array<Object>} An array of homework objects.
     */
    function fetchMockHomework() {
        return [
            {
                isDivisible: false,
                start_date: "2024-07-01T10:00:00",
                due_date: "2024-07-01T12:00:00",
                description: "Math Homework",
                lesson_id: 1,
                student_id: 1,
                timeIndication: 45
            },
            {
                isDivisible: true,
                start_date: "2024-07-02T09:00:00",
                due_date: "2024-07-02T11:00:00",
                description: "Science Homework",
                lesson_id: 2,
                student_id: 2,
                timeIndication: 30
            }
        ];
    }

    /**
     * Populates the calendar with homework data.
     * @param {Array<Object>} homeworks - An array of homework objects.
     */
    function populateCalendar(homeworks) {
        const calendar = document.querySelector('.calendar');
        homeworks.forEach(homework => {
            const dueDate = new Date(homework.due_date);
            const hourBeforeDeadline = new Date(dueDate.getTime() - 60*60*1000);
            const dayOfWeek = hourBeforeDeadline.getDay(); // Sunday - Saturday : 0 - 6
            const timeslot = hourBeforeDeadline.getHours();

            const homeworkDiv = document.createElement('div');
            homeworkDiv.className = 'homework';
            homeworkDiv.textContent = homework.description;
            homeworkDiv.style.gridRow = `${timeslot + 1}`; // assuming first row is header
            homeworkDiv.style.gridColumn = `${dayOfWeek + 1}`; // adjust for your grid structure

            calendar.appendChild(homeworkDiv);
        });
    }

    // Fetch mock data and populate the calendar
    const homeworks = fetchMockHomework();
    populateCalendar(homeworks);
});
