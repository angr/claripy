CELERY_SEND_EVENTS = False

# pickle is necessary and not insecure for our usecase
CELERY_ACCEPT_CONTENT = ['pickle']
