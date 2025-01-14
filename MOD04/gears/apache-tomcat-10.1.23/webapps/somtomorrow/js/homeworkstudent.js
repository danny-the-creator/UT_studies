const centerPopup = document.getElementById('timepopup-form');
const popupOverlay = document.getElementById('timepopup-overlay');
document.addEventListener('DOMContentLoaded', async function()  {
    async function fetchHomeworkCalendar() {
        console.log('running');
        try {
            const response = await fetch(`../../api/homework/${1}/class`);
            if (!response.ok) {
                throw new Error(`HTTP error! status: ${response.status}`);
            }
            const returnedHomework = await response.json();
            console.log('returned homework:', returnedHomework);
            return returnedHomework;
        } catch (error) {
            console.error('Error fetching homework for calendar:', error);
            return []; // Return an empty array or handle error case
        }
    }
    async function fetchLessonTitle(lessonId) {
        try {
            const response = await fetch(`../../api/lesson/${lessonId}`);
            if (!response.ok) {
                throw new Error(`HTTP error! status: ${response.status}`);
            }
            const lesson = await response.json();
            console.log(`Lesson ${lessonId}:`, lesson);
            return lesson.title;
        } catch (error) {
            console.error(`Error fetching lesson ${lessonId}:`, error);
            return "unknown"; // Return "unknown" if there's an error
        }
    }



    async function fetchMockHomework() {
        try {
            const returnedHomework = await fetchHomeworkCalendar();

            // Extract unique lesson IDs
            const lessonIds = [...new Set(returnedHomework.map(hw => hw.lesson_id))];

            // Fetch lesson titles for each unique lesson ID
            const lessonTitles = await Promise.all(lessonIds.map(async (lessonId) => {
                const title = await fetchLessonTitle(lessonId);
                return { lessonId, title };
            }));

            // Create a map of lesson IDs to lesson titles
            const lessonMap = {};
            lessonTitles.forEach(lesson => {
                lessonMap[lesson.lessonId] = lesson.title;
            });

            // Convert the fetched data to the required format
            const formattedHomework = returnedHomework.map(homework => ({
                isDivisible: homework.timeIndication > 30,  // Example condition for isDivisible
                start_date: new Date(homework.start_date).toISOString(),  // Converting timestamp to ISO string
                due_date: new Date(homework.due_date).toISOString(),  // Converting timestamp to ISO string
                subject: lessonMap[homework.lesson_id] || "unknown", // Map lesson title or set to "unknown"
                description: homework.description,
                lesson_id: homework.homework_id, // Assuming lesson_id is equivalent to homework_id
                student_id: 1,  // Assuming a fixed student_id as it is not in the original data
                timeIndication: homework.timeIndication
            }));

            console.log('formatted homework:', formattedHomework);
            return formattedHomework;
        } catch (error) {
            console.error('Error fetching and formatting homework:', error.message || error);
            return []; // Return an empty array or handle error case
        }
    }

    document.addEventListener('DOMContentLoaded', async function() {
        const homeworks = await fetchMockHomework(1);  // Await the fetched homework data
        let currentDate = new Date();

        updateCalendar(homeworks, currentDate);

        const prevWeekButton = document.getElementById('prev-week');
        const nextWeekButton = document.getElementById('next-week');
        const todayButton = document.getElementById('today-button');

        prevWeekButton.addEventListener('click', () => {
            currentDate.setDate(currentDate.getDate() - 7);
            updateCalendar(homeworks, currentDate);
        });

        nextWeekButton.addEventListener('click', () => {
            currentDate.setDate(currentDate.getDate() + 7);
            updateCalendar(homeworks, currentDate);
        });

        todayButton.addEventListener('click', () => {
            currentDate = new Date();
            updateCalendar(homeworks, currentDate);
        });

        attachEventListeners();
    });


    function getWeekStart(date) {
        const currentDate = new Date(date);
        return new Date(currentDate.setDate(currentDate.getDate() - currentDate.getDay() + 1));
    }

    function getWeekEnd(date) {
        const firstDay = getWeekStart(date);
        return new Date(firstDay.setDate(firstDay.getDate() + 4));
    }


    function isDateInCurrentWeek(date, currentWeekStart, currentWeekEnd) {
        const dateObj = new Date(date);
        return dateObj >= currentWeekStart && dateObj <= currentWeekEnd;
    }

    function clearCalendar() {
        const timeslotElements = document.querySelectorAll('.timeslot');
        timeslotElements.forEach(slot => {
            slot.textContent = '_';
            slot.classList.remove('filled-timeslot');
            slot.removeEventListener('mouseenter', showPopup);
            slot.removeEventListener('mouseleave', hidePopup);
        });
    }

    function populateCalendar(homeworks, currentWeekStart, currentWeekEnd) {
        const timeslotElements = document.querySelectorAll('.timeslot');
        homeworks.forEach(homework => {
            if (isDateInCurrentWeek(homework.due_date, currentWeekStart, currentWeekEnd)) {
                const dueDate = new Date(homework.due_date);
                const hourBeforeDeadline = new Date(dueDate.getTime() - 60 * 60 * 1000);
                const dayOfWeek = hourBeforeDeadline.getDay();
                const timeslot = hourBeforeDeadline.getHours();
                const adjustedDayOfWeek = (dayOfWeek === 0 ? 6 : dayOfWeek - 1);
                const index = timeslot * 5 + adjustedDayOfWeek;

                if (timeslotElements[index]) {
                    if (timeslotElements[index].textContent === '_') {
                        timeslotElements[index].textContent = homework.subject;
                        timeslotElements[index].dataset.description = homework.description;
                        timeslotElements[index].dataset.stardate = homework.start_date;
                        timeslotElements[index].dataset.duedate = homework.due_date;
                        timeslotElements[index].dataset.bgColor = "#FFA726";
                        timeslotElements[index].classList.add('filled-timeslot');
                    }
                } else {
                    console.error(`No timeslot found at index ${index}`);
                }
            }
        });

        timeslotElements.forEach(slot => {
            slot.addEventListener('mouseenter', showPopup);
            slot.addEventListener('mouseleave', hidePopup);
        });
    }





    function updateCalendar(homeworks, date) {
        const currentWeekStart = getWeekStart(date);
        const currentWeekEnd = getWeekEnd(date);
        clearCalendar();
        console.log('populating with',homeworks)
        populateCalendar(homeworks, currentWeekStart, currentWeekEnd);
    }

    const homeworks = await fetchMockHomework();
    let currentDate = new Date();

    updateCalendar(homeworks, currentDate);

    const prevWeekButton = document.getElementById('prev-week');
    const nextWeekButton = document.getElementById('next-week');
    const todayButton = document.getElementById('today-button');

    prevWeekButton.addEventListener('click', () => {
        currentDate.setDate(currentDate.getDate() - 7);
        updateCalendar(homeworks, currentDate);
    });

    nextWeekButton.addEventListener('click', () => {
        currentDate.setDate(currentDate.getDate() + 7);
        updateCalendar(homeworks, currentDate);
    });
    todayButton.addEventListener('click', () => { // Add this block
        currentDate = new Date();
        updateCalendar(homeworks, currentDate);
    });


    attachEventListeners();







    const addIconBtn = document.querySelector('.buttonAddIcon');
    const popupForm = document.getElementById('popup-form');
    const popupOverlay = document.getElementById('popup-overlay');
    const addClassBtn = document.getElementById('add-class-btn');






    popupOverlay.addEventListener('click', () => {
        popupForm.style.display = 'none';
        popupOverlay.style.display = 'none';
    });

    addClassBtn.addEventListener('click', () => {
        const className = classNameInput.value.trim();
        if (className) {
            const newCard = document.createElement('a');
            newCard.href = "../classPage/index.html";
            newCard.className = 'card1';
            newCard.style.textDecoration = 'none';
            newCard.innerHTML = `
                <div class="text-content">
                    <div class="title3">Subject Teacher</div>
                    <div class="subtitle1">${className}</div>
                </div>
            `;
            cardParent.appendChild(newCard);
            classNameInput.value = '';
            popupForm.style.display = 'none';
            popupOverlay.style.display = 'none';
        }
    });
});
document.addEventListener('DOMContentLoaded', function() {
    const weekDisplay = document.getElementById('week-display');
    const prevWeekButton = document.getElementById('prev-week');
    const nextWeekButton = document.getElementById('next-week');
    const todayButton = document.getElementById('today-button');

    const calendarContainer = document.querySelector('.calendar-container');
    const currentTimeIndicator = document.getElementById('current-time-indicator');
    let currentDate = new Date();

    function getWeekRange(date) {
        const firstDay = new Date(date.setDate(date.getDate() - date.getDay() + 1));
        const lastDay = new Date(date.setDate(firstDay.getDate() + 4));
        const options = { month: 'short', day: 'numeric', year: 'numeric' };
        return `${firstDay.toLocaleDateString('en-US', options)} - ${lastDay.toLocaleDateString('en-US', options)}`;
    }

    function updateWeekDisplay() {
        weekDisplay.textContent = getWeekRange(new Date(currentDate));
    }



    function animateCalendar(direction) {
        const currentCalendar = document.querySelector('.calendar');
        const newCalendar = currentCalendar.cloneNode(true);

        if (direction === 'left') {
            newCalendar.classList.add('slide-in-left');
            currentCalendar.classList.add('slide-out-right');
        } else {
            newCalendar.classList.add('slide-in-right');
            currentCalendar.classList.add('slide-out-left');
        }

        newCalendar.style.position = 'absolute';
        newCalendar.style.top = '0';
        newCalendar.style.left = '0';
        newCalendar.style.width = '100%';
        newCalendar.style.height = '100%';
        newCalendar.style.zIndex = '1';

        calendarContainer.appendChild(newCalendar);

        setTimeout(() => {
            currentCalendar.remove();
            newCalendar.style.position = '';
            newCalendar.style.top = '';
            newCalendar.style.left = '';
            newCalendar.style.width = '';
            newCalendar.style.height = '';
            newCalendar.style.zIndex = '';
            newCalendar.classList.remove('slide-in-left', 'slide-in-right');
            attachEventListeners();
        }, 500);
    }

    function updateCurrentTimeIndicator() {
        const now = new Date();
        const hours = now.getHours();
        const minutes = now.getMinutes();
        const totalMinutes = hours * 60 + minutes + 2; // Adjusted for 2 minutes

        const timeslotHeight = document.querySelector('.timeslot').offsetHeight;
        const calendarStartOffset = document.querySelector('.time-slot').offsetHeight; // Assuming .time-slot is the header
        const topPosition = (totalMinutes / 60) * timeslotHeight + calendarStartOffset;

        currentTimeIndicator.style.top = `${topPosition}px`;

        // Update the current time display
        const currentTimeDisplay = document.getElementById('current-time-display');
        currentTimeDisplay.style.top = `${topPosition}px`; // Set top to line position
        currentTimeDisplay.textContent = now.toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' });
    }

    prevWeekButton.addEventListener('click', () => {
        currentDate.setDate(currentDate.getDate() - 7);
        updateWeekDisplay();
        animateCalendar('left');
    });

    nextWeekButton.addEventListener('click', () => {
        console.log("no IM being clicked ")
        currentDate.setDate(currentDate.getDate() + 7);
        updateWeekDisplay();
        animateCalendar('right');
    });
    todayButton.addEventListener('click', () => { // Add this block
        console.log("IM being clicked")
        currentDate=new Date();
        updateWeekDisplay();
        animateCalendar('right');
    });

    updateWeekDisplay();
    attachEventListeners();
    updateCurrentTimeIndicator();
    setInterval(updateCurrentTimeIndicator, 60000); // Update every minute
});
var tabText1 = document.getElementById("tabText0");
if (tabText1) {
    tabText1.addEventListener("click", function (e) {
        window.location.href = "../../teacherPages/teacher_profile/index.html";
    });
}
let tabText2 = document.getElementById("tabText1");
if (tabText2) {
    tabText2.addEventListener("click", function (e) {
        window.location.href = "../../login.html?v=" + new Date().getTime();
    });
}
function attachEventListeners() {
    document.querySelectorAll('.timeslot').forEach(slot => {
        slot.addEventListener('mouseenter', showPopup);
        slot.addEventListener('mouseleave', hidePopup);
        slot.addEventListener('click', handleClick);
    });

    popupOverlay.addEventListener('click', function() {
        centerPopup.style.display = 'none';
        popupOverlay.style.display = 'none';
    });

    centerPopup.addEventListener('click', function(event) {
        event.stopPropagation();
    });
}
function showPopup(event) {
    const hoverPopup = document.getElementById('hover-popup');
    const slot = event.currentTarget;
    const rect = slot.getBoundingClientRect();
    hoverPopup.style.left = `${rect.left + window.scrollX}px`;
    hoverPopup.style.top = `${rect.bottom + window.scrollY}px`;
    if (slot.classList.contains('filled-timeslot')) {
        hoverPopup.innerHTML = `<p>${slot.dataset.description}</p>`;
        hoverPopup.style.backgroundColor = slot.dataset.bgColor;
    } else {
        hoverPopup.innerHTML = `<p>No tasks here. Let's keep it that way!</p>`;
        hoverPopup.style.backgroundColor = "#FFFFFF";
    }
    hoverPopup.classList.add('show');
}
function handleClick(event) {
    const slot = event.currentTarget;
    console.log('Timeslot clicked:', slot);
    console.log('Dataset:', slot.dataset);

    if (slot.classList.contains('filled-timeslot')) {
        const startDateTime = slot.dataset.stardate.split('T');
        const dueDateTime = slot.dataset.duedate.split('T');
        const startDate = startDateTime[0];
        const startTime = startDateTime[1];

        const dueDate = dueDateTime[0];
        const dueTime = dueDateTime[1];

        centerPopup.innerHTML = `
            <h2>Homework Details</h2>
            <p><strong>Subject:</strong> ${slot.textContent}</p>
            <p><strong>Description:</strong> ${slot.dataset.description}</p>
             <p><strong>Start Date:</strong> ${startDate}</p>
            <p><strong>Start Time:</strong> ${startTime}</p>
            <p><strong>DueDate:</strong> ${dueDate}</p>
            <p><strong>DueTime:</strong> ${dueTime}</p>
           
            
        `;
    } else {
        // Show something funny
        centerPopup.innerHTML = `
            <h2>Nothing to See Here!</h2>
            <p>Why don't scientists trust atoms? Because they make up everything!</p>
           
        `;
    }
    centerPopup.style.display = 'block';
    popupOverlay.style.display = 'block';


}

function hidePopup() {
    const hoverPopup = document.getElementById('hover-popup');
    hoverPopup.classList.remove('show');
}
